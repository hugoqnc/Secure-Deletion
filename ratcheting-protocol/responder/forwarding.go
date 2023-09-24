package responder

//@ import arb "github.com/ModularVerification/ReusableVerificationLibrary/arbitrary"
//@ import ev "github.com/ModularVerification/ReusableVerificationLibrary/event"
//@ import "github.com/ModularVerification/ReusableVerificationLibrary/label"
//@ import labeledlib "github.com/ModularVerification/ReusableVerificationLibrary/labeledlibrary/library"
//@ import "github.com/ModularVerification/ReusableVerificationLibrary/labeling"
//@ import p "github.com/ModularVerification/ReusableVerificationLibrary/principal"
//@ import tm "github.com/ModularVerification/ReusableVerificationLibrary/term"
//@ import tr "github.com/ModularVerification/ReusableVerificationLibrary/trace"
//@ import u "github.com/ModularVerification/ReusableVerificationLibrary/usage"

import lib "github.com/ModularVerification/casestudies/wireguard/library"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/common"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/labellemma"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/labellemma/common"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/labellemma/responder"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/messages/common"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/messages/responder"
//@ import pap "github.com/ModularVerification/casestudies/wireguard/verification/pattern"


// trusted wrapper around the library's `GetPacket` function
// to express that the returned payload can only be sent to
// this actor's session or its peer but no one else. In particular, this
// stops an implementation of sending out the payload (i.e. a VPN packet)
// in plaintext to the network.
//@ trusted
//@ requires acc(ResponderMem(responder), 1/2)
//@ ensures  acc(ResponderMem(responder), 1/2)
//@ ensures  ok ==> labeledlib.Mem(res) && tm.gamma(term) == labeledlib.Abs(res)
//@ ensures  ok ==> GetWgLabeling().IsMsg(responder.Snapshot(), term, label.Readers(set[p.Id]{ responder.getAId(), responder.getBSessId() }))
func (responder *Responder) GetPacket() (res lib.ByteString, ok bool /*@, ghost term tm.Term @*/) {
	//@ unfold acc(ResponderMem(responder), 1/2)
	res, ok /*@, term @*/ = responder.LibState.GetPacket()
	//@ fold acc(ResponderMem(responder), 1/2)
	return
}

//@ requires ResponderMem(responder) && lib.ConnectionMem(conn)
//@ requires lib.ConnectionSendKey(conn) == tm.gamma(kriT)
//@ requires lib.ConnectionRecvKey(conn) == tm.gamma(kirT)
//@ requires lib.ConnectionNonceVal(conn) == 0
//@ requires responder.transportKeysLabelingBeforeRecvFirstMsg(epkIX, ekrT, kirT, kriT, aSess, corrupted)
//@ requires GetWgLabeling().NonceForEventIsUnique(ekrT, ReceivedFirstResp)
//@ requires unfolding ResponderMem(responder) in responder.llib.Version() == 0
//@ requires labeledlib.guard(0) && labeledlib.guardNext(1)
func (responder *Responder) forwardPackets(conn *lib.Connection /*@, ghost epkIX tm.Term, ghost ekrT tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost corrupted bool, ghost aSess uint32 @*/) {

	//@ ghost isFirstReceive := true
	//@ responder.proveSecurityProperties(epkIX, ekrT, kirT, kriT, aSess, corrupted)

	// Verification that the initial send key satisfies the sendMessage preconditions
	// TODO_ move into a lemma
	//@ bSessAId := label.Readers(set[p.Id]{ responder.getBSessId(), responder.getAId() })
	//@ aIdBSess := label.Readers(set[p.Id]{ responder.getAId(), responder.getBSessId() })

	//@ ctx := GetWgLabeling()
	//@ t := responder.Snapshot()
	// Verification for kirT
	//@ assert ctx.IsValid(t, kirT)
	//@ assert ctx.IsSecretRelaxed(t, kirT, aIdBSess, u.AeadKey(WgKir))
	//@ assert GetWgLabeling().IsAeadKey(t, kirT, aIdBSess, WgKir)
	// Verification for kriT
	//@ assert ctx.IsValid(t, kriT)
	//@ assert ctx.IsSecretRelaxed(t, kriT, aIdBSess, u.AeadKey(WgKri))
	//@ assert ctx.IsAeadKey(t, kriT, aIdBSess, WgKri)
	//@ assert set[p.Id]{ responder.getAId(), responder.getBSessId() } == set[p.Id]{ responder.getBSessId(), responder.getAId() }
	//@ assert aIdBSess == bSessAId
	//@ assert ctx.IsAeadKey(responder.Snapshot(), kriT, bSessAId, WgKri)

	ghost if !corrupted {
		
		// Prove that the initial key flows to B's session (meaning that it is unversioned)
		//@ assert ctx.GetLabel(kirT) == Label_k_IR(responder.getASessId(aSess), responder.getBSessId())
		//@ ProveKirFlowsToBSess(ctx, t, responder.getASessId(aSess), responder.getBSessId())
		//@ assert ctx.CanFlow(responder.Snapshot(), GetWgLabeling().GetLabel(kirT), label.Readers(set[p.Id]{ responder.getBSessId() }))

		// Unfold `ConnectionMem` to access memory predicates of the initial keys
		//@ unfold lib.ConnectionMem(conn)
		//@ assert acc(conn)
		//@ assert labeledlib.Mem(conn.RecvKey) && labeledlib.Abs(conn.RecvKey) == tm.gamma(kirT)
		//@ assert labeledlib.Mem(conn.SendKey) && labeledlib.Abs(conn.SendKey) == tm.gamma(kriT)

		// RECEIVE 0
		ok, newK, newDhIHalfKey /*@, newKT, newDhIHalfKeyT @*/ := responder.receiveMessage(conn.RecvKey, nil, nil, conn, 0 /*@, kirT, tm.zeroString(0), tm.zeroString(0), 1/100, 0 @*/)
		if !ok {
			return
		}
		//@ unfold ResponderMem(responder)
		//@ responder.llib.ApplyMonotonicity()
		//@ fold ResponderMem(responder)
		//@ t = responder.Snapshot()
		
		// SEND 0
		msg, ok /*@, msgT @*/ := responder.GetPacket()
		if !ok {
			return
		}
		ok, _, newDhPrivateKey /*@, _, newDhPrivateKeyT @*/ := responder.sendMessage(msg, conn.SendKey, nil, nil, conn, 0 /*@, msgT, kriT, tm.zeroString(0), tm.zeroString(0), 1/100, 0 @*/)
		if !ok {
			return
		}
		//@ unfold ResponderMem(responder)
		//@ responder.llib.ApplyMonotonicity()
		//@ fold ResponderMem(responder)
		// Proving monotonicity of IsAeadKey for newK
		// //@ ctx.IsValidMonotonic(t, responder.Snapshot(), newKT)
		// //@ ctx.CanFlowMonotonic(t, responder.Snapshot(), label.Readers(set[p.Id]{ responder.getBSessId(), responder.getAId() }), ctx.GetLabel(newKT)) 
		// //@ assert ctx.IsAeadKey(responder.Snapshot(), newKT, label.Readers(set[p.Id]{ responder.getBSessId(), responder.getAId() }), WgKir)
		
		// RECEIVE 1
		ok, newK, newDhIHalfKey /*@, newKT, newDhIHalfKeyT @*/ := responder.receiveMessage(newK, newDhPrivateKey, newDhIHalfKey, conn, 1 /*@, newKT, newDhPrivateKeyT, newDhIHalfKeyT, 1/100, 0 @*/)
		if !ok {
			return
		}
		//@ unfold ResponderMem(responder)
		//@ responder.llib.ApplyMonotonicity()
		//@ fold ResponderMem(responder)
		
		// SEND 1
		msg, ok /*@, msgT @*/ := responder.GetPacket()
		if !ok {
			return
		}
		ok, newK, newDhPrivateKey /*@, newKT, newDhPrivateKeyT @*/ := responder.sendMessage(msg, newK, newDhPrivateKey, newDhIHalfKey, conn, 1 /*@, msgT, newKT, newDhPrivateKeyT, newDhIHalfKeyT, 1/100, 1 @*/)
		if !ok {
			return
		}
		//@ unfold ResponderMem(responder)
		//@ responder.llib.ApplyMonotonicity()
		//@ fold ResponderMem(responder)

		// RECEIVE 2
		ok, newK, newDhIHalfKey /*@, newKT, newDhIHalfKeyT @*/ := responder.receiveMessage(newK, newDhPrivateKey, newDhIHalfKey, conn, 2 /*@, newKT, newDhPrivateKeyT, newDhIHalfKeyT, 1/100, 1 @*/)
		if !ok {
			return
		}
		//@ unfold ResponderMem(responder)
		//@ responder.llib.ApplyMonotonicity()
		//@ fold ResponderMem(responder)

		// SEND 2
		msg, ok /*@, msgT @*/ := responder.GetPacket()
		if !ok {
			return
		}
		ok, newK, newDhPrivateKey /*@, newKT, newDhPrivateKeyT @*/ := responder.sendMessage(msg, newK, newDhPrivateKey, newDhIHalfKey, conn, 2 /*@, msgT, newKT, newDhPrivateKeyT, newDhIHalfKeyT, 1/100, 2 @*/)
		if !ok {
			return
		}
		//@ unfold ResponderMem(responder)
		//@ responder.llib.ApplyMonotonicity()
		//@ fold ResponderMem(responder)

		// Assert remaining guards
		//@ assert acc(labeledlib.guard(2), 99/100)
		//@ assert acc(labeledlib.guardNext(3), 99/100)
		//@ assert acc(labeledlib.receipt(newK, 2), 1/100)
		//@ assert acc(labeledlib.receipt(newDhPrivateKey, 3), 1/100)
	}


// 	//@ invariant ResponderMem(responder) && lib.ConnectionMem(conn)
// 	//@ invariant lib.ConnectionSendKey(conn) == tm.gamma(kriT)
// 	//@ invariant lib.ConnectionRecvKey(conn) == tm.gamma(kirT)
// 	//@ invariant lib.ConnectionNonceVal(conn) >= 0
// 	//@ invariant isFirstReceive ==> GetWgLabeling().NonceForEventIsUnique(ekrT, ReceivedFirstResp)
// 	//@ invariant isFirstReceive ==> responder.transportKeysLabelingBeforeRecvFirstMsg(epkIX, ekrT, kirT, kriT, aSess, corrupted)
// 	//@ invariant isFirstReceive ==> transportKeysWeakForwardSecrecy(responder.Snapshot(), epkIX, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId())
// 	//@ invariant !isFirstReceive ==> responder.transportKeysLabelingAfterRecvFirstMsg(ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted)
// 	//@ invariant !isFirstReceive ==> transportKeysStrongForwardSecrecy(responder.Snapshot(), ekiT, epkIX, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId())
// 	//@ invariant !isFirstReceive ==> responder.InjectiveAgreementWithKCIResistance(responder.getASessId(aSess), responder.getBSessId(), receivedFirstRespEv(ekiT, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId()), sendFirstInitEv(ekiT, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId()))
// 	for {

// 		var response lib.ByteString
// 		var done bool = false // ADAPT

// 		//@ invariant ResponderMem(responder) && acc(lib.ConnectionMem(conn), 1/2)
// 		//@ invariant lib.ConnectionSendKey(conn) == tm.gamma(kriT)
// 		//@ invariant lib.ConnectionRecvKey(conn) == tm.gamma(kirT)
// 		//@ invariant (!done && isFirstReceive) ==> responder.transportKeysLabelingBeforeRecvFirstMsg(epkIX, ekrT, kirT, kriT, aSess, corrupted)
// 		//@ invariant (!done && isFirstReceive) ==> GetWgLabeling().NonceForEventIsUnique(ekrT, ReceivedFirstResp)
// 		//@ invariant (done || !isFirstReceive) ==> responder.transportKeysLabelingAfterRecvFirstMsg(ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted)
// 		//@ invariant  done ==> labeledlib.Mem(response)
// 		for !done {
// 			response, done /*@, ekiT, aSess, corrupted @*/ = responder.receiveMessage(conn /*@, ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted, isFirstReceive @*/)
// 		}
// 		//@ isFirstReceive = false


// 		//@ ghost rid := responder.getRid()
// 		//@ unfold ResponderMem(responder)
// 		(responder.LibState).ConsumePacket(response)
// 		//@ fold ResponderMem(responder)
// 		request, ok /*@, msgT @*/ := responder.GetPacket()
// 		if ok {
// 			//@ s1 := responder.Snapshot()
// 			responder.sendMessage(request, conn /*@, ekiT, epkIX, ekrT, kirT, kriT, msgT, corrupted, aSess @*/)
// 			//@ unfold ResponderMem(responder)
// 			//@ responder.llib.ApplyMonotonicity()
// 			//@ fold ResponderMem(responder)
// 			//@ responder.transportKeysLabelingAfterRecvFirstMsgMonotonic(s1, ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted)
// 		}

// 		// with the following statement, we show that we can prove the specified
// 		// security properties after each iteration of the transport phase:
// 		//@ responder.proveSecurityPropertiesAfter(ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted)
// 	}
}

//@ requires iteration >= 0 && versionPerm > 0
//@ requires ResponderMem(responder) && acc(conn)
//@ requires iteration == 0 ==> conn.Nonce == 0
//@ requires iteration > 0 ==> conn.Nonce > 0
//@ requires unfolding ResponderMem(responder) in responder.llib.Version() == currentVersion
// msg properties
//@ requires labeledlib.Mem(msg) && labeledlib.Abs(msg) == tm.gamma(msgT)
//@ requires GetWgLabeling().IsMsg(responder.Snapshot(), msgT, label.Readers(set[p.Id]{ responder.getBSessId(), responder.getAId() })) // This is what we get from `GetPacket`
// K properties
//@ requires labeledlib.Mem(K) && labeledlib.Abs(K) == tm.gamma(KT) && labeledlib.Size(K) == 32
//@ requires iteration == 0 ==> GetWgLabeling().IsAeadKey(responder.Snapshot(), KT, label.Readers(set[p.Id]{ responder.getBSessId(), responder.getAId() }), WgKri)
//@ requires iteration > 0  ==> GetWgLabeling().IsAeadKey(responder.Snapshot(), KT, label.Readers(set[p.Id]{ responder.getBPreviousVersionId(), responder.getBVersionId(), responder.getAId() }), WgKVersIr)
// //@ requires iteration == 0 ==> GetWgLabeling().CanFlow(responder.Snapshot(), GetWgLabeling().GetLabel(KT), label.Readers(set[p.Id]{ responder.getBSessId() }))
// dhPrivateKey properties
//@ requires iteration > 0 ==> labeledlib.Mem(dhPrivateKey) && labeledlib.Abs(dhPrivateKey) == tm.gamma(dhPrivateKeyT) && dhPrivateKeyT == tm.random(labeledlib.Abs(dhPrivateKey), label.Readers(set[p.Id]{ responder.getBPreviousVersionId(), responder.getBVersionId() }), u.DhKey(WgDHSK)) && labeledlib.Size(dhPrivateKey) == 32 && GetWgLabeling().IsValid(responder.Snapshot(), dhPrivateKeyT) // If iteration == 0, the parameter dhPrivateKey is not used
// dhIHalfKey properties
//@ requires iteration > 0 ==> labeledlib.Mem(dhIHalfKey) && labeledlib.Abs(dhIHalfKey) == tm.gamma(dhIHalfKeyT) // If iteration == 0, the parameter dhIHalfKey is not used
//@ requires iteration > 0 ==> exists e tm.Term :: {tm.exp(tm.generator(), e)} dhIHalfKeyT == tm.exp(tm.generator(), e) && GetWgLabeling().CanFlow(responder.Snapshot(), label.Readers(set[p.Id]{ responder.getAId() }), GetWgLabeling().GetLabel(e)) && e.IsRandom() && labeledlib.Size(dhIHalfKey) == labeledlib.DHHalfKeyLength && GetWgLabeling().IsValid(responder.Snapshot(), dhIHalfKeyT) && GetWgLabeling().GetUsage(dhIHalfKeyT) == some(u.DhKey(WgDHHK))
// guard properties
//@ requires iteration == 0 ==> acc(labeledlib.guard(currentVersion), versionPerm) && acc(labeledlib.guardNext(currentVersion+1), versionPerm)
//@ requires iteration > 0  ==> acc(labeledlib.guard(currentVersion), 2*versionPerm) && acc(labeledlib.guardNext(currentVersion+1), versionPerm) && acc(labeledlib.receipt(dhPrivateKey, currentVersion), versionPerm) && acc(labeledlib.receipt(K, currentVersion), versionPerm)
//@ ensures ResponderMem(responder) && acc(conn)
//@ ensures responder.ImmutableState() == old(responder.ImmutableState())
//@ ensures  old(responder.Snapshot()).isSuffix(responder.Snapshot())
//@ ensures ok ==> conn.Nonce > 0
// newK properties
//@ ensures ok ==> labeledlib.Mem(newK) && labeledlib.Abs(newK) == tm.gamma(newKT) && labeledlib.Size(newK) == 32
//@ ensures ok && iteration == 0 ==> GetWgLabeling().IsAeadKey(responder.Snapshot(), newKT, label.Readers(set[p.Id]{ responder.getBSessId(), responder.getAId() }), WgKri)
//@ ensures ok && iteration > 0  ==> GetWgLabeling().IsAeadKey(responder.Snapshot(), newKT, label.Readers(set[p.Id]{ responder.getBPreviousVersionId(), responder.getBVersionId(), responder.getAId() }), WgKVersRi)
// //@ ensures ok && iteration == 0 ==> GetWgLabeling().CanFlow(responder.Snapshot(), GetWgLabeling().GetLabel(newKT), label.Readers(set[p.Id]{ responder.getBSessId() })) // This is to prove that newK == K is not versioned when decrypting the first message
// newDhPrivateKey properties
//@ ensures ok ==> labeledlib.Mem(newDhPrivateKey) && labeledlib.Abs(newDhPrivateKey) == tm.gamma(newDhPrivateKeyT) && newDhPrivateKeyT == tm.random(labeledlib.Abs(newDhPrivateKey), label.Readers(set[p.Id]{ responder.getBVersionId(), responder.getBNextVersionId() }), u.DhKey(WgDHSK)) && GetWgLabeling().IsValid(responder.Snapshot(), newDhPrivateKeyT) && labeledlib.Size(newDhPrivateKey) == 32
// dhIHalfKey properties
//@ ensures iteration > 0 ==> labeledlib.Mem(dhIHalfKey) && labeledlib.Abs(dhIHalfKey) == tm.gamma(dhIHalfKeyT)
//@ ensures iteration > 0 ==> exists e tm.Term :: {tm.exp(tm.generator(), e)} dhIHalfKeyT == tm.exp(tm.generator(), e) && GetWgLabeling().CanFlow(responder.Snapshot(), label.Readers(set[p.Id]{ responder.getAId() }), GetWgLabeling().GetLabel(e)) && e.IsRandom() && labeledlib.Size(dhIHalfKey) == labeledlib.DHHalfKeyLength && GetWgLabeling().IsValid(responder.Snapshot(), dhIHalfKeyT) && GetWgLabeling().GetUsage(dhIHalfKeyT) == some(u.DhKey(WgDHHK))
// guard properties
//@ ensures ok && iteration == 0 ==> acc(labeledlib.guard(currentVersion), 1*versionPerm) && acc(labeledlib.receipt(newDhPrivateKey, currentVersion + 1), versionPerm)
//@ ensures ok && iteration > 0  ==> acc(labeledlib.guard(currentVersion), 3*versionPerm) && acc(labeledlib.receipt(newK, currentVersion), versionPerm) && acc(labeledlib.receipt(newDhPrivateKey, currentVersion + 1), versionPerm)
// TODO_ add the corrupted bool to handle corruption?
func (responder *Responder) sendMessage(msg lib.ByteString, K lib.ByteString, dhPrivateKey lib.ByteString, dhIHalfKey lib.ByteString, conn *lib.Connection, iteration int /*@, ghost msgT tm.Term, ghost KT tm.Term, ghost dhPrivateKeyT tm.Term, ghost dhIHalfKeyT tm.Term, ghost versionPerm perm, ghost currentVersion uint32 @*/) (ok bool, newK lib.ByteString, newDhPrivateKey lib.ByteString /*@, ghost newKT tm.Term, ghost newDhPrivateKeyT tm.Term @*/) {
	// Useful constants
	//@ ctx := GetWgLabeling()
	//@ t := responder.Snapshot()
	//@ bId := responder.getBId()
	//@ bSessId := responder.getBSessId()
	//@ bVersId := responder.getBVersionId()
	//@ bNextVersId := responder.getBNextVersionId()
	//@ bPreviousVersId := responder.getBPreviousVersionId()
	//@ aId := responder.getAId()

	// Verification of entry term usages
	//@ assert  iteration == 0 ==> ctx.GetUsage(KT) == some(u.AeadKey(WgKri))
	//@ assert iteration > 0 ==> ctx.GetUsage(KT) == some(u.AeadKey(WgKVersIr))
	//@ assert iteration > 0 ==> ctx.GetUsage(dhIHalfKeyT) == some(u.DhKey(WgDHHK))
	//@ assert iteration > 0 ==> ctx.GetUsage(dhPrivateKeyT) == some(u.DhKey(WgDHSK))
	
	// If iteration > 0, derive newK with KDF from K, dhIHalfKey and the ephemeral key
	/*@
	keyLabel := label.Readers(set[p.Id]{ bPreviousVersId, bVersId, aId })
	ghost if iteration == 0 {
		keyLabel = label.Readers(set[p.Id]{ bSessId, aId })
	}
	@*/

	if iteration == 0 {
		newK = K
		newKT = KT
		//@ assert labeledlib.Mem(newK)
		//@ assert labeledlib.Abs(newK) == tm.gamma(newKT)
		//@ assert ctx.IsAeadKey(t, newKT, keyLabel, WgKri)
		//@ assert ctx.GetUsage(newKT) == some(u.AeadKey(WgKri))
	} else {
		//@ unfold ResponderMem(responder)
		dhSharedSecret, err := responder.llib.DhSharedSecret(dhPrivateKey, dhIHalfKey)
		//@ fold ResponderMem(responder)
		//@ ghost dhSharedSecretT := tm.exp(dhIHalfKeyT, dhPrivateKeyT)
		ok = err == nil
		if !ok {
			return
		}
		//@ assert labeledlib.Abs(dhSharedSecret) == tm.gamma(dhSharedSecretT)

		// Verify that `dhSharedSecretT` indeed has a WgDHSS usage
		//@ ProveSharedSecretUsage(ctx, dhIHalfKeyT, dhPrivateKeyT, dhSharedSecretT)
		//@ assert ctx.GetUsage(dhSharedSecretT) == some(u.DhKey(WgDHSS))

		newK = lib.NewByteString(32)
		//@ unfold ResponderMem(responder)
		lib.ComputeKDFRatchet(newK, K, dhSharedSecret /*@, currentVersion, versionPerm @*/)
		//@ fold ResponderMem(responder)
		//@ newKT = Term_ratchet(KT, dhSharedSecretT)
		ok = err == nil
		if !ok {
			return
		}
		//@ assert labeledlib.Abs(newK) == tm.gamma(newKT)

		// Verify that `newKT` indeed has a WgKVersRi usage
		//@ ProveVersionedKeyUsage(ctx, false, true, newKT)
		//@ assert ctx.GetUsage(newKT) == some(u.AeadKey(WgKVersRi))

		// Verifying that `newKT` indeed IsAeadKey
		//@ ProveIsAeadKey(ctx, t, keyLabel, KT, newKT, dhPrivateKeyT, dhSharedSecretT, aId, bVersId, bPreviousVersId, WgKVersRi)
		//@ assert ctx.IsAeadKey(t, newKT, keyLabel, WgKVersRi)
	}

	// Create ephemeral key
	//@ t0 := t
	//@ assert t0 == old(responder.Snapshot())
	var err error
	//@ unfold ResponderMem(responder)
	//@ assert responder.llib.OwnerWithVersion().Covers(responder.llib.OwnerWithVersion())
	// The ephemeral key has the current and next versions
	newDhPrivateKey, err /*@, newDhPrivateKeyT @*/ = responder.llib.GenerateDHKey(/*@ label.Readers(set[p.Id]{ responder.llib.OwnerWithVersion(), responder.llib.OwnerWithNextVersion() }), versionPerm, WgDHSK, set[ev.EventType]{ } @*/) // TODO_ add event(s)
	//@ responder.llib.ApplyMonotonicity()
	//@ fold ResponderMem(responder)
	ok = err == nil
	if !ok {
		return
	}
	//@ assert acc(labeledlib.receipt(newDhPrivateKey, currentVersion), versionPerm)
	//@ t = responder.Snapshot()
	//@ t1 := t
	//@ assert t0.isSuffix(t1)

	// After creating newDhPrivateKey, it should be converted to the next version (when iteration > 0) to allow for a later bump
	//@ unfold ResponderMem(responder)
	//@ assert responder.llib.OwnerWithNextVersion().Covers(responder.llib.OwnerWithNextVersion())
	//@ responder.llib.ConvertToNextVersion(newDhPrivateKey, newDhPrivateKeyT, versionPerm)
	//@ fold ResponderMem(responder)
	//@ assert acc(labeledlib.receipt(newDhPrivateKey, currentVersion + 1), versionPerm)

	// Obtain the associated public key
	//@ unfold ResponderMem(responder)
	dhRHalfKey, err := responder.llib.DhExp(newDhPrivateKey /*@, newDhPrivateKeyT @*/)
	//@ t = responder.llib.Snapshot()
	//@ fold ResponderMem(responder)
	//@ ghost dhRHalfKeyT := tm.exp(tm.generator(), newDhPrivateKeyT)
	ok = err == nil
	if !ok {
		return
	}
	//@ assert labeledlib.Abs(dhRHalfKey) == tm.gamma(dhRHalfKeyT)
	//@ assert labeledlib.Size(dhRHalfKey) == labeledlib.DHHalfKeyLength

	// Verify that `dhRHalfKeyT` indeed has a WgDHHK usage
	//@ ProveHalfKeyUsage(ctx, dhRHalfKeyT, newDhPrivateKeyT)
	//@ assert ctx.GetUsage(dhRHalfKeyT) == some(u.DhKey(WgDHHK))

	// Delete (old) dhPrivateKey
	if iteration > 0 {
		//@ unfold ResponderMem(responder)
		err = responder.llib.DeleteSafely(dhPrivateKey /*@, versionPerm, versionPerm @*/)
		//@ fold ResponderMem(responder)
		ok = err == nil
		if !ok {
			return
		}
	}

	// Delete K
	if iteration > 0 {
		//@ unfold ResponderMem(responder)
		err = responder.llib.DeleteSafely(K /*@, versionPerm, versionPerm @*/)
		//@ fold ResponderMem(responder)
		ok = err == nil
		if !ok {
			return
		}
	}

	// Get encryption nonce
	if conn.Nonce >= 18446744073709543423 {
		ok = false
		return
	}
	var nonce uint64
	if conn.Nonce == 0 {
		nonce = 0
	} else {
		nonce = lib.GetCounter(conn.Nonce)
	}
	nonceBytes := lib.NonceToBytes(nonce)

	// Encrypt the message with newK
	//@ assert labeledlib.Size(newK) == 32
	//@ unfold ResponderMem(responder)
	plaintext := (responder.LibState).PadMsg(msg)

	//____________ Proving AeadEnc ________________________________
	// TODO_ move (a part of) the proof to a lemma?
	//@ t := responder.llib.Snapshot()

	//@ assert ctx.IsLabeledRelaxed(t, newKT, keyLabel)
	//@ assert iteration == 0 ==> ctx.IsAeadKey(t, newKT, keyLabel, WgKri)
	//@ assert iteration > 0  ==> ctx.IsAeadKey(t, newKT, keyLabel, WgKVersRi)
	//@ assert exists usageString string :: ctx.IsAeadKey(t, newKT, keyLabel, usageString) // Necessary to prove `CanAeadEncrypt`
	//@ assert ctx.IsPublishable(t, tm.integer64(nonce))
	//@ assert ctx.IsPublishable(t, dhRHalfKeyT)

	//@ assert ctx.IsValid(t, msgT)
	//@ if iteration == 0 {
		//@ assert bSessId.Covers(bSessId)
		//@ assert aId.Covers(aId)
		//@ assert labeling.includesIds(set[p.Id]{ bSessId, aId }, set[p.Id]{ bSessId, aId })
		//@ assert ctx.CanFlow(t, label.Readers(set[p.Id]{ bSessId, aId }), keyLabel)
		//@ ctx.CanFlowTransitive(t, ctx.GetLabel(msgT), label.Readers(set[p.Id]{ bSessId, aId }), keyLabel)
		//@ assert ctx.CanFlow(t, ctx.GetLabel(msgT), keyLabel)
	//@ } else {
		//@ assert aId.Covers(aId)
		//@ assert bSessId.Covers(bPreviousVersId)
		//@ assert bSessId.Covers(bVersId)
		//@ assert labeling.includesIds(set[p.Id]{ bSessId, aId }, set[p.Id]{ bPreviousVersId, bVersId, aId })
		//@ assert ctx.CanFlow(t, label.Readers(set[p.Id]{ bSessId, aId }), label.Readers(set[p.Id]{ bPreviousVersId, bVersId, aId }))
		//@ assert ctx.CanFlow(t, label.Readers(set[p.Id]{ bSessId, aId }), keyLabel)
		//@ ctx.CanFlowTransitive(t, ctx.GetLabel(msgT), label.Readers(set[p.Id]{ bSessId, aId }), keyLabel)
		//@ assert ctx.CanFlow(t, ctx.GetLabel(msgT), keyLabel)
	//@ }
	//@ assert ctx.CanFlow(t, ctx.GetLabel(msgT), keyLabel)
	//@ assert ctx.IsMsg(t, msgT, keyLabel)

	//@ assert exists e tm.Term :: {tm.exp(tm.generator(), e)} dhRHalfKeyT == tm.exp(tm.generator(), e) && e.IsRandom() && GetWgLabeling().GetUsage(dhRHalfKeyT) == some(u.DhKey(WgDHHK)) && t.OnlyNonceOccurs(e)
	//@ assert exists e tm.Term :: {tm.exp(tm.generator(), e)} dhRHalfKeyT == tm.exp(tm.generator(), e) && e.IsRandom() && GetWgLabeling().GetUsage(dhRHalfKeyT) == some(u.DhKey(WgDHHK)) && ctx.GetLabel(e) == label.Readers(set[p.Id]{ bVersId, bNextVersId }) && t.OnlyNonceOccurs(e)
	//@ assert bId.Covers(bVersId)
	//@ assert bId.Covers(bNextVersId)
	//@ assert labeling.includesIds(set[p.Id]{ bId }, set[p.Id]{ bVersId, bNextVersId })
	//@ assert ctx.CanFlow(t, label.Readers(set[p.Id]{ bId }), label.Readers(set[p.Id]{ bVersId, bNextVersId }))
	//@ assert bId == lib.principalId(1)
	//@ assert bId == p.principalId(lib.Principal(1))
	//@ assert ctx.CanFlow(t, label.Readers(set[p.Id]{ p.principalId(lib.Principal(1)) }), label.Readers(set[p.Id]{ bVersId, bNextVersId }))
	//@ assert exists e tm.Term :: {tm.exp(tm.generator(), e)} dhRHalfKeyT == tm.exp(tm.generator(), e) && e.IsRandom() && GetWgLabeling().GetUsage(dhRHalfKeyT) == some(u.DhKey(WgDHHK)) && GetWgLabeling().CanFlow(t, label.Readers(set[p.Id]{ p.principalId(lib.Principal(1)) }), GetWgLabeling().GetLabel(e)) && t.OnlyNonceOccurs(e)

	//@ assert GetWgUsage().versionedRiPayloadPred(t, dhRHalfKeyT)
	//@ assert iteration == 0 ==> GetWgUsage().AeadPred(t, WgKri, newKT, tm.integer64(nonce), msgT, dhRHalfKeyT)
	//@ assert iteration > 0  ==> GetWgUsage().AeadPred(t, WgKVersRi, newKT, tm.integer64(nonce), msgT, dhRHalfKeyT)
	//@ assert (forall usageString string :: ctx.IsAeadKey(t, newKT, keyLabel, usageString) ==> ctx.usage.AeadPred(t, usageString, newKT, tm.integer64(nonce), msgT, dhRHalfKeyT))

	//@ assert ctx.CanAeadEncrypt(t, newKT, tm.integer64(nonce), msgT, dhRHalfKeyT, keyLabel)
	//______________________________________________________________
	encryptedMsg, err := responder.llib.AeadEnc(newK, nonceBytes, plaintext, dhRHalfKey /*@, newKT, tm.integer64(nonce), msgT, dhRHalfKeyT, keyLabel @*/)
	//@ fold ResponderMem(responder)
	ok = err == nil
	if !ok {
		return
	}

	// Construct the message
	message := &lib.Message{
		Type:     4,
		Receiver: conn.RemoteIndex,
		Nonce:    nonce,
		Data:     dhRHalfKey,
		Payload:  encryptedMsg,
	}
	//@ sidR := tm.integer32B(conn.RemoteIndex)
	//@ sidrT := tm.integer32(conn.RemoteIndex)
	packet := lib.MarshalMessage(message)
	//@ packetT := tm.tuple5(tm.integer32(4), sidrT, tm.integer64(nonce), dhRHalfKeyT, tm.aead(newKT, tm.integer64(nonce), msgT, dhRHalfKeyT))
	//@ assert labeledlib.Abs(packet) == tm.gamma(packetT)
	conn.Nonce += 1

	// Prove the message invariant: the packet is publishable
	//@ assert ctx.IsValid(t, tm.integer64(nonce))
	//@ assert ctx.IsValid(t, msgT)
	//@ assert ctx.IsValid(t, dhRHalfKeyT)
	//@ assert ctx.IsValidAead(t, newKT, tm.integer64(nonce), msgT, ctx.GetLabel(msgT), dhRHalfKeyT)
	//@ ctx.IsMsgTupleCreate(t, packetT, label.Public())

	// Send the message
	//@ unfold ResponderMem(responder)
	err = responder.llib.Send(lib.Principal(responder.b), lib.Principal(responder.a), packet /*@, packetT @*/)
	ok = err == nil
	//@ responder.llib.ApplyMonotonicity()
	//@ fold ResponderMem(responder)
	//@ t2 := responder.Snapshot()
	//@ assert t1.isSuffix(t2)

	// Necessary postconditions verification
	//@ assert t0 == old(responder.Snapshot()) && t0.isSuffix(t1) && t1.isSuffix(t2)
	//@ t0.isSuffixTransitive(t1, t2)
	//@ assert old(responder.Snapshot()).isSuffix(responder.Snapshot())
	//@ ghost if iteration == 0 {
		//@ ctx.IsAeadKey(t1, newKT, keyLabel, WgKri)
		//@ ctx.IsValidMonotonic(t1, responder.Snapshot(), newKT)
		//@ ctx.CanFlowMonotonic(t1, responder.Snapshot(), label.Readers(set[p.Id]{ responder.getBSessId(), responder.getAId() }), ctx.GetLabel(newKT)) 
		//@ assert ctx.IsAeadKey(responder.Snapshot(), newKT, label.Readers(set[p.Id]{ responder.getBSessId(), responder.getAId() }), WgKri)
	//@ }
	//@ assert iteration == 0 ==> GetWgLabeling().IsAeadKey(responder.Snapshot(), newKT, label.Readers(set[p.Id]{ responder.getBSessId(), responder.getAId() }), WgKri)

	return
}


//@ requires iteration >= 0 && versionPerm > 0 && versionPerm < 1/2
//@ requires ResponderMem(responder)
//@ requires unfolding ResponderMem(responder) in responder.llib.Version() == currentVersion
// K properties
//@ requires labeledlib.Mem(K) && labeledlib.Abs(K) == tm.gamma(KT) && labeledlib.Size(K) == 32
//@ requires iteration <= 1 ==> GetWgLabeling().IsAeadKey(responder.Snapshot(), KT, label.Readers(set[p.Id]{ responder.getBSessId(), responder.getAId() }), WgKir)
//@ requires iteration > 1  ==> GetWgLabeling().IsAeadKey(responder.Snapshot(), KT, label.Readers(set[p.Id]{ responder.getBPreviousVersionId(), responder.getBVersionId(), responder.getAId() }), WgKVersRi)
//@ requires iteration == 0 ==> GetWgLabeling().CanFlow(responder.Snapshot(), GetWgLabeling().GetLabel(KT), label.Readers(set[p.Id]{ responder.getBSessId() })) // This is to prove that newK == K is not versioned when decrypting the first message
// dhPrivateKey properties
//@ requires iteration > 0 ==> labeledlib.Mem(dhPrivateKey) && labeledlib.Abs(dhPrivateKey) == tm.gamma(dhPrivateKeyT) && dhPrivateKeyT == tm.random(labeledlib.Abs(dhPrivateKey), label.Readers(set[p.Id]{ responder.getBVersionId(), responder.getBNextVersionId() }), u.DhKey(WgDHSK)) && GetWgLabeling().IsValid(responder.Snapshot(), dhPrivateKeyT) && labeledlib.Size(dhPrivateKey) == 32
// dhIHalfKey properties
//@ requires iteration > 0 ==> labeledlib.Mem(dhIHalfKey) && labeledlib.Abs(dhIHalfKey) == tm.gamma(dhIHalfKeyT) // If iteration == 0, the parameter dhIHalfKey is not used
//@ requires iteration > 0 ==> exists e tm.Term :: {tm.exp(tm.generator(), e)} dhIHalfKeyT == tm.exp(tm.generator(), e) && GetWgLabeling().CanFlow(responder.Snapshot(), label.Readers(set[p.Id]{ responder.getAId() }), GetWgLabeling().GetLabel(e)) && e.IsRandom() && labeledlib.Size(dhIHalfKey) == labeledlib.DHHalfKeyLength && GetWgLabeling().IsValid(responder.Snapshot(), dhIHalfKeyT) && GetWgLabeling().GetUsage(dhIHalfKeyT) == some(u.DhKey(WgDHHK))
// guard properties
//@ requires iteration == 0 ==> acc(labeledlib.guard(currentVersion), 2*versionPerm)
//@ requires iteration == 1 ==> versionPerm < 1/4 && acc(labeledlib.guard(currentVersion), 1/1) && acc(labeledlib.guardNext(currentVersion+1), 1/1 - versionPerm)
//@ requires iteration > 1  ==> versionPerm < 1/4 && acc(labeledlib.guard(currentVersion), 1/1 - versionPerm) && acc(labeledlib.guardNext(currentVersion+1), 1/1 - versionPerm) && acc(labeledlib.receipt(K, currentVersion), versionPerm)
//@ ensures  ResponderMem(responder)
//@ ensures  responder.ImmutableStateExceptVersion() == old(responder.ImmutableStateExceptVersion())
//@ ensures responder.Snapshot() == old(responder.Snapshot())
//@ ensures  old(responder.Snapshot()).isSuffix(responder.Snapshot())
//@ ensures unfolding ResponderMem(responder) in ok ==> (iteration == 0 ? responder.llib.Version() == currentVersion : responder.llib.Version() == currentVersion + 1)
// newK properties
//@ ensures ok ==> labeledlib.Mem(newK) && labeledlib.Abs(newK) == tm.gamma(newKT) && labeledlib.Size(newK) == 32
//@ ensures ok && iteration == 0 ==> GetWgLabeling().IsAeadKey(responder.Snapshot(), newKT, label.Readers(set[p.Id]{ responder.getBSessId(), responder.getAId() }), WgKir)
//@ ensures ok && iteration > 0  ==> GetWgLabeling().IsAeadKey(responder.Snapshot(), newKT, label.Readers(set[p.Id]{ responder.getBPreviousVersionId(), responder.getBVersionId(), responder.getAId() }), WgKVersIr)
// newDhIHalfKey properties
//@ ensures  ok ==> labeledlib.Mem(newDhIHalfKey) && labeledlib.Abs(newDhIHalfKey) == tm.gamma(newDhIHalfKeyT)
//@ ensures  ok ==> exists e tm.Term :: {tm.exp(tm.generator(), e)} newDhIHalfKeyT == tm.exp(tm.generator(), e) && GetWgLabeling().CanFlow(responder.Snapshot(), label.Readers(set[p.Id]{ responder.getAId() }), GetWgLabeling().GetLabel(e)) && e.IsRandom() && labeledlib.Size(newDhIHalfKey) == labeledlib.DHHalfKeyLength && GetWgLabeling().IsValid(responder.Snapshot(), newDhIHalfKeyT) && GetWgLabeling().GetUsage(newDhIHalfKeyT) == some(u.DhKey(WgDHHK))
// dhPrivateKey properties
//@ ensures ok && iteration > 0 ==> labeledlib.Mem(dhPrivateKey) && labeledlib.Abs(dhPrivateKey) == tm.gamma(dhPrivateKeyT) && dhPrivateKeyT == tm.random(labeledlib.Abs(dhPrivateKey), label.Readers(set[p.Id]{ responder.getBPreviousVersionId(), responder.getBVersionId() }), u.DhKey(WgDHSK)) && GetWgLabeling().IsValid(responder.Snapshot(), dhPrivateKeyT) && labeledlib.Size(dhPrivateKey) == 32
// guard properties
//@ ensures  ok && iteration == 0 ==> acc(labeledlib.guard(currentVersion), 2*versionPerm)
//@ ensures  ok && iteration > 0  ==> acc(labeledlib.guard(currentVersion+1), 1/1 - 2*versionPerm) && acc(labeledlib.guardNext(currentVersion+2), 1/1) && acc(labeledlib.receipt(newK, currentVersion+1), versionPerm)
func (responder *Responder) receiveMessage(K lib.ByteString, dhPrivateKey lib.ByteString, dhIHalfKey lib.ByteString, conn *lib.Connection, iteration int /*@, ghost KT tm.Term, ghost dhPrivateKeyT tm.Term, ghost dhIHalfKeyT tm.Term, ghost versionPerm perm, ghost currentVersion uint32 @*/) (ok bool , newK lib.ByteString, newDhIHalfKey lib.ByteString /*@, ghost newKT tm.Term, ghost newDhIHalfKeyT tm.Term @*/) {

	// Receive the packet
	//@ unfold acc(ResponderMem(responder), 1/8)
	packet, err /*@, term @*/ := responder.LibState.Receive(lib.Principal(responder.a), lib.Principal(responder.b) /*@, responder.llib.Snapshot() @*/)
	ok = err == nil
	//@ fold acc(ResponderMem(responder), 1/8)
	if !ok {
		return
	}

	message, ok := lib.UnmarshalMessage(packet)
	if !ok {
		return
	}

	ok = message.Type == 4
	if !ok {
		return
	}

	//@ unfold acc(ResponderMem(responder), 1/8)
	//@ unfold acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), 1/8)
	ok = (responder.HandshakeInfo).LocalIndex == message.Receiver
	//@ fold acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), 1/8)
	//@ fold acc(ResponderMem(responder), 1/8)
	if !ok {
		return
	}

	// Useful constants
	/*@
	ctx := GetWgLabeling()
	t := responder.Snapshot()
	aId := responder.getAId()
	bId := responder.getBId()
	bSessId := responder.getBSessId()
	bVersId := responder.getBVersionId()
	bNextVersId := responder.getBNextVersionId()
	keyLabel := label.Readers(set[p.Id]{ bVersId, bNextVersId, aId })
	ghost if iteration == 0 {
		keyLabel = label.Readers(set[p.Id]{ bSessId, aId })
	}
	@*/

	// Assume that the obtained term is a 5-tuple 
	/*@
	nonceBytes := lib.NonceToBytes(message.Nonce)

	newDhIHalfKey := message.Data
	newDhIHalfKeyT := tm.oneTerm(labeledlib.Abs(newDhIHalfKey))

	unfold ResponderMem(responder)
	responder.llib.MessageOccursImpliesMessageInv(aId.getPrincipal(), bId.getPrincipal(), term)
	fold ResponderMem(responder)
	predictedPayloadT := tm.oneTerm(labeledlib.Abs(message.Payload))
	ghost if term.IsTuple5() {
		predictedPayloadT = tm.getTupleElem(term, 4)
		// we can transfer knowledge about `term` only to its components if we
		// assume that it's a 5-tuple, i.e. has the expected shape as this is not
		// implied by the fact that `message.Payload` is a `tuple5B`.
		// therefore, we obtain here these facts only under an implication.
		// this implication is then resolved when applying the pattern property at
		// the very end of the parsing process.
		ctx.IsMsgTupleResolve(t, term, label.Public())
	}
	assert labeledlib.Abs(message.Payload) == tm.gamma(predictedPayloadT)
	assert term.IsTuple5() ==> ctx.IsPublishable(t, predictedPayloadT)
	@*/

	// Useful variables
	/*@
	var plaintext lib.ByteString
	ghost var m tm.Bytes
	n := tm.integer64B(message.Nonce)
	a := labeledlib.Abs(message.Data)
	ghost var msgTX tm.Term
	ghost var nonceTX tm.Term
	ghost var adTX tm.Term
	@*/

	if iteration == 0 {
		// K remains the same, and is used to decrypt the message
		newK = K
		newKT = KT
		//@ assert labeledlib.Mem(newK)
		//@ assert labeledlib.Abs(newK) == tm.gamma(newKT)
		//@ assert ctx.IsAeadKey(t, newKT, keyLabel, WgKir)

		//@ unfold ResponderMem(responder)
		plaintext, err = responder.llib.AeadDec(newK, nonceBytes, message.Payload, newDhIHalfKey /*@, 0/1, newKT, tm.integer64(message.Nonce), predictedPayloadT, newDhIHalfKeyT, keyLabel @*/)
		//@ fold ResponderMem(responder)
		ok = err == nil
		if !ok { // ADAPT
			return
		}

		// Proving obtention of `AeadPred`
		//@ m = labeledlib.Abs(plaintext)
		//@ rid := responder.getRid()
		//@ unfold acc(ResponderMem(responder), 1/4)
		//@ fold pap.pattern4Constraints(responder.llib, aId, WgKir, rid, newKT)
		//@ nonceTX, msgTX, adTX = pap.patternProperty4(responder.llib, aId, WgKir, rid, newKT, tm.oneTerm(n), tm.oneTerm(m),  tm.oneTerm(a), term)
		//@ unfold pap.pattern4Constraints(responder.llib, aId, WgKir, rid, newKT)
		//@ fold acc(ResponderMem(responder), 1/4)
		//@ assert ctx.IsValidAead(t, newKT, nonceTX, msgTX, ctx.GetLabel(msgTX), adTX)
		//@ assert ctx.IsPublishable(t, newKT) || GetWgUsage().AeadPred(t, u.GetUsageString(get(ctx.GetUsage(newKT))), newKT, nonceTX, msgTX, adTX)
		
	} else {		
		// Obtain the DH shared secret (from the public key given in the associated data, and the private key)
		//@ unfold ResponderMem(responder)
		dhSharedSecret, err := responder.llib.DhSharedSecret(dhPrivateKey, dhIHalfKey)
		//@ ghost dhSharedSecretT := tm.exp(dhIHalfKeyT, dhPrivateKeyT)

		//@ ProveSharedSecretUsage(ctx, dhIHalfKeyT, dhPrivateKeyT, dhSharedSecretT)
		//@ assert ctx.GetUsage(dhSharedSecretT) == some(u.DhKey(WgDHSS))

		//@ fold ResponderMem(responder)
		ok = err == nil
		if !ok {
			return
		}
		//@ assert labeledlib.Abs(dhSharedSecret) == tm.expB(labeledlib.Abs(dhIHalfKey), labeledlib.Abs(dhPrivateKey))
		//@ assert labeledlib.Abs(dhSharedSecret) == tm.gamma(dhSharedSecretT)

		// Obtain newK
		newK = lib.NewByteString(32)
		//@ unfold ResponderMem(responder)
		lib.ComputeKDFRatchet(newK, K, dhSharedSecret /*@, currentVersion, versionPerm @*/)
		//@ fold ResponderMem(responder)
		//@ newKT = Term_ratchet(KT, dhSharedSecretT)
		ok = err == nil
		if !ok {
			return
		}
		//@ assert labeledlib.Abs(newK) == tm.gamma(newKT)

		// Verify that `newKT` indeed has a WgKVersIr usage
		//@ ProveVersionedKeyUsage(ctx, iteration==1, false, newKT)
		//@ assert ctx.GetUsage(newKT) == some(u.AeadKey(WgKVersIr))

		// Verifying that `newKT` indeed IsAeadKey
		//@ ProveIsAeadKey(ctx, t, keyLabel, KT, newKT, dhPrivateKeyT, dhSharedSecretT, aId, bNextVersId, bVersId, WgKVersIr)
		//@ assert ctx.IsAeadKey(t, newKT, keyLabel, WgKVersIr)

		// After creating newK, it should be converted to the next version (when iteration > 0) to allow for a later bump
		//@ assert exists e tm.Term :: {tm.exp(tm.generator(), e)} ctx.GetLabel(newKT) == label.Join(ctx.GetLabel(e), label.Readers(set[p.Id]{ bVersId, bNextVersId }))
		//@ ProveNewKFlowsToOwnerWithVersion(ctx, t, newKT, aId, bVersId, bNextVersId)
		//@ unfold ResponderMem(responder)
		//@ assert ctx.CanFlow(t, ctx.GetLabel(newKT), label.Readers(set[p.Id]{ responder.llib.OwnerWithNextVersion() }))
		//@ responder.llib.ConvertToNextVersion(newK, newKT, versionPerm)
		//@ fold ResponderMem(responder)
		//@ assert acc(labeledlib.receipt(newK, currentVersion + 1), versionPerm)

		// Delete K when iteration > 1
		if iteration > 1 {
			//@ unfold ResponderMem(responder)
			err = responder.llib.DeleteSafely(K /*@, versionPerm, versionPerm @*/)
			//@ fold ResponderMem(responder)
			ok = err == nil
			if !ok {
				return
			}
		}

		// Decrypt the message
		//@ unfold ResponderMem(responder)
		plaintext, err = responder.llib.AeadDec(newK, nonceBytes, message.Payload, newDhIHalfKey /*@, versionPerm, newKT, tm.integer64(message.Nonce), predictedPayloadT, newDhIHalfKeyT, keyLabel @*/)
		//@ fold ResponderMem(responder)
		ok = err == nil
		if !ok { // ADAPT
			return
		}

		// Proving obtention of `AeadPred`
		//@ m = labeledlib.Abs(plaintext)
		//@ rid := responder.getRid()
		//@ unfold acc(ResponderMem(responder), 1/4)
		//@ fold pap.pattern4Constraints(responder.llib, aId, WgKVersIr, rid, newKT)
		//@ nonceTX, msgTX, adTX = pap.patternProperty4(responder.llib, aId, WgKVersIr, rid, newKT, tm.oneTerm(n), tm.oneTerm(m),  tm.oneTerm(a), term)
		//@ unfold pap.pattern4Constraints(responder.llib, aId, WgKVersIr, rid, newKT)
		//@ fold acc(ResponderMem(responder), 1/4)
		//@ assert ctx.IsValidAead(t, newKT, nonceTX, msgTX, ctx.GetLabel(msgTX), adTX)
		//@ assert ctx.IsPublishable(t, newKT) || GetWgUsage().AeadPred(t, u.GetUsageString(get(ctx.GetUsage(newKT))), newKT, nonceTX, msgTX, adTX)
	}

	//@ assert ctx.IsPublishable(t, newKT) || GetWgUsage().versionedIrPayloadPred(t, adTX)

	// Disjunction of `IsPublishable` and `versionedIrPayloadPred`
	/*@
	ghost if ctx.IsPublishable(t, newKT) {
		// TODO_ do something related to corruption
		ok = false
		return
	}
	
	assert GetWgUsage().versionedIrPayloadPred(t, adTX)
	assert exists e tm.Term :: {tm.exp(tm.generator(), e)} adTX == tm.exp(tm.generator(), e) && e.IsRandom() && GetWgLabeling().GetUsage(adTX) == some(u.DhKey(WgDHHK)) && GetWgLabeling().CanFlow(t, label.Readers(set[p.Id]{ aId }), ctx.GetLabel(e)) && ctx.IsValid(t, adTX)

	assert labeledlib.Mem(message.Data) && labeledlib.Abs(message.Data) == tm.gamma(adTX) && labeledlib.Size(message.Data) == labeledlib.DHHalfKeyLength

	// Write results in returned values
	newDhIHalfKey = message.Data
	newDhIHalfKeyT = adTX
	@*/


	// Delete the message (except the initial one that is not versioned)
	if iteration > 0 {
		// TODO_ should `receiveMessage` return the decrypted message? It is not necessary just for the sake of the protocol. Currently, we delete it right after decryption, but we could add a function call that does something with the message before deleting it.
		//@ unfold ResponderMem(responder)
		err = responder.llib.DeleteSafely(plaintext /*@, versionPerm, versionPerm @*/)
		//@ fold ResponderMem(responder)
		ok = err == nil
		if !ok {
			return
		}
	}


	// Bump the version
	//@ if iteration > 0 {
		//@ unfold ResponderMem(responder)
		//@ responder.llib.BumpVersion(1/1 - 2*versionPerm)
		//@ fold ResponderMem(responder)
		//@ assert unfolding ResponderMem(responder) in responder.llib.Version() == currentVersion + 1
	//@ }
	//@ assert unfolding ResponderMem(responder) in iteration == 0 ? responder.llib.Version() == currentVersion : responder.llib.Version() == currentVersion + 1

	// Properties after bumping
	//@ assert iteration == 0 ==> ctx.IsAeadKey(t, newKT, keyLabel, WgKir) // No bump in this case
	//@ keyLabelAfterBump := label.Readers(set[p.Id]{ responder.getBPreviousVersionId(), responder.getBVersionId(), aId })
	//@ assert iteration > 0  ==> ctx.IsAeadKey(t, newKT, keyLabelAfterBump, WgKVersIr)
	return
}

