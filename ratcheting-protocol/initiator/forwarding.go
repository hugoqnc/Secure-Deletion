package initiator

//@ import arb "github.com/ModularVerification/ReusableVerificationLibrary/arbitrary"
//@ import ev "github.com/ModularVerification/ReusableVerificationLibrary/event"
//@ import "github.com/ModularVerification/ReusableVerificationLibrary/label"
//@ import labeledlib "github.com/ModularVerification/ReusableVerificationLibrary/labeledlibrary/library"
//@ import "github.com/ModularVerification/ReusableVerificationLibrary/labeling"
//@ import p "github.com/ModularVerification/ReusableVerificationLibrary/principal"
//@ import tm "github.com/ModularVerification/ReusableVerificationLibrary/term"
//@ import u "github.com/ModularVerification/ReusableVerificationLibrary/usage"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/common"

import lib "github.com/ModularVerification/casestudies/wireguard/library"
//@ import .   "github.com/ModularVerification/casestudies/wireguard/verification/messages/initiator"
//@ import pap "github.com/ModularVerification/casestudies/wireguard/verification/pattern"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/labellemma"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/labellemma/common"


// trusted wrapper around the library's `GetPacket` function
// to express that the returned payload can only be sent to
// this actor's session or its peer but no one else. In particular, this
// stops an implementation of sending out the payload (i.e. a VPN packet)
// in plaintext to the network.
//@ trusted
//@ requires acc(InitiatorMem(initiator), 1/2)
//@ ensures  acc(InitiatorMem(initiator), 1/2)
//@ ensures  ok ==> labeledlib.Mem(res) && tm.gamma(term) == labeledlib.Abs(res)
//@ ensures  ok ==> GetWgLabeling().IsMsg(initiator.Snapshot(), term, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }))
func (initiator *Initiator) GetPacket() (res lib.ByteString, ok bool /*@, ghost term tm.Term @*/) {
	//@ unfold acc(InitiatorMem(initiator), 1/2)
	res, ok /*@, term @*/ = initiator.LibState.GetPacket()
	//@ fold acc(InitiatorMem(initiator), 1/2)
	return
}

//@ requires InitiatorMem(initiator) && lib.ConnectionMem(conn)
//@ requires lib.ConnectionSendKey(conn) == tm.gamma(kirT)
//@ requires lib.ConnectionRecvKey(conn) == tm.gamma(kriT)
//@ requires initiator.transportKeysLabeling(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
//@ requires lib.ConnectionNonceVal(conn) == 0
//@ requires unfolding InitiatorMem(initiator) in initiator.llib.Version() == 0
//@ requires labeledlib.guard(0) && labeledlib.guardNext(1)
func (initiator *Initiator) forwardPackets(conn *lib.Connection /*@, ghost ekiT tm.Term, ghost epkRX tm.Term, ghost ekRX tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost bSess uint32, ghost corrupted bool @*/) {

	//@ ghost var isFirstMessage bool = true
	//@ initiator.proveSecurityProperties(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)

	// Verification that the initial send key satisfies the sendMessage preconditions
	//@ aSessBId := label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() })
	//@ assert set[p.Id]{ initiator.getASessId(), initiator.getBId() } == set[p.Id]{ initiator.getBId(), initiator.getASessId() }
	//@ assert aSessBId == label.Readers(set[p.Id]{ initiator.getBId(), initiator.getASessId() })
	//@ unfold InitiatorMem(initiator)
	//@ ctx := GetWgLabeling()
	//@ t := initiator.llib.Snapshot()
	//@ assert ctx.IsValid(t, kirT)
	//@ assert GetWgLabeling().IsAeadKey(t, kirT, aSessBId, WgKir)
	//@ assert GetWgUsage().hasKirStructure(kirT)
	//@ fold InitiatorMem(initiator)

	ghost if !corrupted {

		// Prove that the initial key flows to B's session (meaning that it is unversioned)
		//@ assert ctx.GetLabel(kriT) == Label_k_RI(initiator.getASessId(), initiator.getBSessId(bSess))
		//@ ProveKriFlowsToASess(ctx, t, initiator.getASessId(), initiator.getBSessId(bSess))
		//@ assert ctx.CanFlow(initiator.Snapshot(), GetWgLabeling().GetLabel(kriT), label.Readers(set[p.Id]{ initiator.getASessId() }))

		// Unfold `ConnectionMem` to access memory predicates of the initial keys
		//@ unfold lib.ConnectionMem(conn)
		//@ assert acc(conn)
		//@ assert labeledlib.Mem(conn.SendKey) && labeledlib.Abs(conn.SendKey) == tm.gamma(kirT)
		//@ assert labeledlib.Mem(conn.RecvKey) && labeledlib.Abs(conn.RecvKey) == tm.gamma(kriT)

		// SEND 0
		msg, ok /*@, msgT @*/ := initiator.GetPacket()
		if !ok {
			return
		}
		ok, newK, newDhPrivateKey /*@, newKT, newDhPrivateKeyT @*/  := initiator.sendMessage(msg, conn.SendKey, nil, nil, conn, 0 /*@, msgT, kirT, tm.zeroString(0), tm.zeroString(0), 1/100, 0 @*/)
		if !ok {
			return
		}
		//@ unfold InitiatorMem(initiator)
		//@ initiator.llib.ApplyMonotonicity()
		//@ fold InitiatorMem(initiator)
		//@ t = initiator.Snapshot()

		// RECEIVE 0
		ok, _, newDhIHalfKey /*@, _, newDhIHalfKeyT @*/ := initiator.receiveMessage(conn.RecvKey, nil, nil, conn, 0 /*@, kriT, tm.zeroString(0), tm.zeroString(0), 1/100, 0 @*/)
		if !ok {
			return
		}
		//@ unfold InitiatorMem(initiator)
		//@ initiator.llib.ApplyMonotonicity()
		//@ fold InitiatorMem(initiator)
		// Proving monotonicity of IsAeadKey for newK
		// //@ ctx.IsValidMonotonic(t, initiator.Snapshot(), newKT)
		// //@ ctx.CanFlowMonotonic(t, initiator.Snapshot(), label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), ctx.GetLabel(newKT)) 
		// //@ assert ctx.IsAeadKey(initiator.Snapshot(), newKT, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), WgKir)
		
		// SEND 1
		msg, ok /*@, msgT @*/ := initiator.GetPacket()
		if !ok {
			return
		}
		ok, newK, newDhPrivateKey /*@, newKT, newDhPrivateKeyT @*/  := initiator.sendMessage(msg, newK, newDhPrivateKey, newDhIHalfKey, conn, 1 /*@, msgT, newKT, newDhPrivateKeyT, newDhIHalfKeyT, 1/100, 1 @*/)
		if !ok {
			return
		}
		//@ unfold InitiatorMem(initiator)
		//@ initiator.llib.ApplyMonotonicity()
		//@ fold InitiatorMem(initiator)

		// RECEIVE 1
		ok, newK, newDhIHalfKey /*@, newKT, newDhIHalfKeyT @*/ := initiator.receiveMessage(newK, newDhPrivateKey, newDhIHalfKey, conn, 1 /*@, newKT, newDhPrivateKeyT, newDhIHalfKeyT, 1/100, 1 @*/)
		if !ok {
			return
		}
		//@ unfold InitiatorMem(initiator)
		//@ initiator.llib.ApplyMonotonicity()
		//@ fold InitiatorMem(initiator)

		// SEND 2
		msg, ok /*@, msgT @*/ := initiator.GetPacket()
		if !ok {
			return
		}
		ok, newK, newDhPrivateKey /*@, newKT, newDhPrivateKeyT @*/  := initiator.sendMessage(msg, newK, newDhPrivateKey, newDhIHalfKey, conn, 2 /*@, msgT, newKT, newDhPrivateKeyT, newDhIHalfKeyT, 1/100, 2 @*/)
		if !ok {
			return
		}
		//@ unfold InitiatorMem(initiator)
		//@ initiator.llib.ApplyMonotonicity()
		//@ fold InitiatorMem(initiator)

		// RECEIVE 2
		ok, newK, newDhIHalfKey /*@, newKT, newDhIHalfKeyT @*/ := initiator.receiveMessage(newK, newDhPrivateKey, newDhIHalfKey, conn, 2 /*@, newKT, newDhPrivateKeyT, newDhIHalfKeyT, 1/100, 2 @*/)
		if !ok {
			return
		}
		//@ unfold InitiatorMem(initiator)
		//@ initiator.llib.ApplyMonotonicity()
		//@ fold InitiatorMem(initiator)

		// Assert remaining guards
		//@ assert acc(labeledlib.guard(3), 98/100)
		//@ assert acc(labeledlib.guardNext(4), 100/100)
		//@ assert acc(labeledlib.receipt(newK, 3), 1/100)
		//@ assert acc(labeledlib.receipt(newDhPrivateKey, 3), 1/100)
	}

	

// 	//@ invariant InitiatorMem(initiator) && lib.ConnectionMem(conn)
// 	//@ invariant lib.ConnectionSendKey(conn) == tm.gamma(kirT)
// 	//@ invariant lib.ConnectionRecvKey(conn) == tm.gamma(kriT)
// 	//@ invariant initiator.transportKeysLabeling(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
// 	//@ invariant  isFirstMessage ==> lib.ConnectionNonceVal(conn) == 0
// 	//@ invariant !isFirstMessage ==> lib.ConnectionNonceVal(conn) > 0
// 	//@ invariant transportKeysStrongForwardSecrecy(initiator.Snapshot(), ekiT, epkRX, ekRX, kirT, kriT, initiator.getASessId(), initiator.getBSessId(bSess))
// 	//@ invariant initiator.InjectiveAgreementWithKCIResistance(initiator.getASessId(), initiator.getBSessId(bSess), sendFirstInitEv(ekiT, ekRX, kirT, kriT, initiator.getASessId(), initiator.getBSessId(bSess)), sendSidREv(tm.exp(tm.generator(), ekiT), ekRX, kirT, kriT, initiator.getASessId(), initiator.getBSessId(bSess)))
// 	for {
// 		//@ ghost rid := initiator.getRid()
// 		//@ ghost s0 := initiator.Snapshot()
// 		var request lib.ByteString
// 		var ok bool
// 		//@ ghost var term tm.Term
// 		request, ok /*@, term @*/ = initiator.GetPacket()
		
// 		if ok {
// 			//@ ghost var isInState3 bool
// 			ok /*@, isInState3 @*/ = initiator.sendMessage(request, conn /*@, isFirstMessage, ekiT, epkRX, ekRX, kirT, kriT, term, bSess, corrupted @*/)
// 			//@ isFirstMessage = !isInState3
// 			//@ initiator.transportKeysLabelingMonotonic(s0, ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)

// 			if ok {
// 				var response lib.ByteString
// 				var done bool = false // ADAPT
// 				//@ invariant InitiatorMem(initiator) && acc(lib.ConnectionMem(conn), 1/4)
// 				//@ invariant done ==> labeledlib.Mem(response)
// 				//@ invariant lib.ConnectionSendKey(conn) == tm.gamma(kirT)
// 				//@ invariant lib.ConnectionRecvKey(conn) == tm.gamma(kriT)
// 				//@ invariant initiator.transportKeysLabeling(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
// 				for !done {
					// //@ ghost s1 := initiator.Snapshot()
// 					response, done = initiator.receiveMessage(conn /*@, kirT, kriT @*/)
					// //@ initiator.transportKeysLabelingMonotonic(s1, ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
// 				}

// 				//@ unfold acc(InitiatorMem(initiator), 1/2)
// 				(initiator.LibState).ConsumePacket(response)
// 				//@ fold acc(InitiatorMem(initiator), 1/2)
// 			}
// 		}

// 		// with the following statement, we show that we can prove the specified
// 		// security properties after each iteration of the transport phase:
// 		//@ initiator.proveSecurityProperties(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
// 	}
}

//@ requires iteration >= 0 && versionPerm > 0
//@ requires InitiatorMem(initiator) && acc(conn)
//@ requires iteration == 0 ==> acc(labeledlib.Mem(conn.RecvKey)) && labeledlib.Size(conn.RecvKey) == 32
//@ requires iteration == 0 ==> conn.Nonce == 0
//@ requires iteration > 0 ==> conn.Nonce > 0
//@ requires unfolding InitiatorMem(initiator) in initiator.llib.Version() == currentVersion
// msg properties
//@ requires labeledlib.Mem(msg) && labeledlib.Abs(msg) == tm.gamma(msgT)
//@ requires GetWgLabeling().IsMsg(initiator.Snapshot(), msgT, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() })) // This is what we get from `GetPacket`
// K properties
//@ requires labeledlib.Mem(K) && labeledlib.Abs(K) == tm.gamma(KT) && labeledlib.Size(K) == 32
//@ requires iteration <= 1 ==> GetWgLabeling().IsAeadKey(initiator.Snapshot(), KT, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), WgKir)
//@ requires iteration > 1  ==> GetWgLabeling().IsAeadKey(initiator.Snapshot(), KT, label.Readers(set[p.Id]{ initiator.getAPreviousVersionId(), initiator.getAVersionId(), initiator.getBId() }), WgKVersRi)
// dhPrivateKey properties
//@ requires iteration > 0 ==> labeledlib.Mem(dhPrivateKey) && labeledlib.Abs(dhPrivateKey) == tm.gamma(dhPrivateKeyT) && dhPrivateKeyT == tm.random(labeledlib.Abs(dhPrivateKey), label.Readers(set[p.Id]{ initiator.getAPreviousVersionId(), initiator.getAVersionId() }), u.DhKey(WgDHSK)) && labeledlib.Size(dhPrivateKey) == 32 && GetWgLabeling().IsValid(initiator.Snapshot(), dhPrivateKeyT) // If iteration == 0, the parameter dhPrivateKey is not used
// dhRHalfKey properties
//@ requires iteration > 0 ==> labeledlib.Mem(dhRHalfKey) && labeledlib.Abs(dhRHalfKey) == tm.gamma(dhRHalfKeyT) // If iteration == 0, the parameter dhRHalfKey is not used
//@ requires iteration > 0 ==> exists e tm.Term :: {tm.exp(tm.generator(), e)} dhRHalfKeyT == tm.exp(tm.generator(), e) && GetWgLabeling().CanFlow(initiator.Snapshot(), label.Readers(set[p.Id]{ initiator.getBId() }), GetWgLabeling().GetLabel(e)) && e.IsRandom() && labeledlib.Size(dhRHalfKey) == labeledlib.DHHalfKeyLength && GetWgLabeling().IsValid(initiator.Snapshot(), dhRHalfKeyT) && GetWgLabeling().GetUsage(dhRHalfKeyT) == some(u.DhKey(WgDHHK))
// guard properties
//@ requires iteration == 0 ==> acc(labeledlib.guard(currentVersion), versionPerm) && acc(labeledlib.guardNext(currentVersion+1), versionPerm)
//@ requires iteration == 1 ==> acc(labeledlib.guard(currentVersion), 2*versionPerm) && acc(labeledlib.guardNext(currentVersion+1), versionPerm) && acc(labeledlib.receipt(dhPrivateKey, currentVersion), versionPerm)
//@ requires iteration > 1  ==> acc(labeledlib.guard(currentVersion), 2*versionPerm) && acc(labeledlib.guardNext(currentVersion+1), versionPerm) && acc(labeledlib.receipt(dhPrivateKey, currentVersion), versionPerm) && acc(labeledlib.receipt(K, currentVersion), versionPerm)
//@ ensures InitiatorMem(initiator) && acc(conn)
//@ ensures initiator.ImmutableState() == old(initiator.ImmutableState())
//@ ensures  old(initiator.Snapshot()).isSuffix(initiator.Snapshot())
//@ ensures ok ==> conn.Nonce > 0
//@ ensures iteration == 0 ==> acc(labeledlib.Mem(conn.RecvKey)) && labeledlib.Abs(conn.RecvKey) == old(labeledlib.Abs(conn.RecvKey)) && labeledlib.Size(conn.RecvKey) == 32
// newK properties
//@ ensures ok ==> labeledlib.Mem(newK) && labeledlib.Abs(newK) == tm.gamma(newKT) && labeledlib.Size(newK) == 32
//@ ensures ok && iteration == 0 ==> GetWgLabeling().IsAeadKey(initiator.Snapshot(), newKT, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), WgKir)
//@ ensures ok && iteration > 0  ==> GetWgLabeling().IsAeadKey(initiator.Snapshot(), newKT, label.Readers(set[p.Id]{ initiator.getAPreviousVersionId(), initiator.getAVersionId(), initiator.getBId() }), WgKVersIr)
// newDhPrivateKey properties
//@ ensures ok ==> labeledlib.Mem(newDhPrivateKey) && labeledlib.Abs(newDhPrivateKey) == tm.gamma(newDhPrivateKeyT) && newDhPrivateKeyT == tm.random(labeledlib.Abs(newDhPrivateKey), label.Readers(set[p.Id]{ initiator.getAVersionId(), initiator.getANextVersionId() }), u.DhKey(WgDHSK)) && GetWgLabeling().IsValid(initiator.Snapshot(), newDhPrivateKeyT) && labeledlib.Size(newDhPrivateKey) == 32
// dhRHalfKey properties
//@ ensures iteration > 0 ==> labeledlib.Mem(dhRHalfKey) && labeledlib.Abs(dhRHalfKey) == tm.gamma(dhRHalfKeyT)
//@ ensures iteration > 0 ==> exists e tm.Term :: {tm.exp(tm.generator(), e)} dhRHalfKeyT == tm.exp(tm.generator(), e) && GetWgLabeling().CanFlow(initiator.Snapshot(), label.Readers(set[p.Id]{ initiator.getBId() }), GetWgLabeling().GetLabel(e)) && e.IsRandom() && labeledlib.Size(dhRHalfKey) == labeledlib.DHHalfKeyLength && GetWgLabeling().IsValid(initiator.Snapshot(), dhRHalfKeyT) && GetWgLabeling().GetUsage(dhRHalfKeyT) == some(u.DhKey(WgDHHK))
// guard properties
//@ ensures ok && iteration == 0 ==> acc(labeledlib.guard(currentVersion), 1*versionPerm) && acc(labeledlib.receipt(newDhPrivateKey, currentVersion + 1), versionPerm)
//@ ensures ok && iteration == 1 ==> acc(labeledlib.guard(currentVersion), 2*versionPerm) && acc(labeledlib.receipt(newK, currentVersion), versionPerm) && acc(labeledlib.receipt(newDhPrivateKey, currentVersion + 1), versionPerm)
//@ ensures ok && iteration > 1  ==> acc(labeledlib.guard(currentVersion), 3*versionPerm) && acc(labeledlib.receipt(newK, currentVersion), versionPerm) && acc(labeledlib.receipt(newDhPrivateKey, currentVersion + 1), versionPerm)
// TODO_ add the corrupted bool to handle corruption?
func (initiator *Initiator) sendMessage(msg lib.ByteString, K lib.ByteString, dhPrivateKey lib.ByteString, dhRHalfKey lib.ByteString, conn *lib.Connection, iteration int /*@, ghost msgT tm.Term, ghost KT tm.Term, ghost dhPrivateKeyT tm.Term, ghost dhRHalfKeyT tm.Term, ghost versionPerm perm, ghost currentVersion uint32 @*/) (ok bool, newK lib.ByteString, newDhPrivateKey lib.ByteString /*@, ghost newKT tm.Term, ghost newDhPrivateKeyT tm.Term @*/) {
	// Useful constants
	//@ ctx := GetWgLabeling()
	//@ t := initiator.Snapshot()
	//@ aId := initiator.getAId()
	//@ aSessId := initiator.getASessId()
	//@ aVersId := initiator.getAVersionId()
	//@ aNextVersId := initiator.getANextVersionId()
	//@ aPreviousVersId := initiator.getAPreviousVersionId()
	// //@ bSessId := initiator.getBSessId(bSess)
	//@ bId := initiator.getBId()

	// Verification of entry term usages
	//@ assert  iteration <= 1 ==> ctx.GetUsage(KT) == some(u.AeadKey(WgKir))
	//@ assert iteration > 1 ==> ctx.GetUsage(KT) == some(u.AeadKey(WgKVersRi))
	//@ assert iteration > 0 ==> ctx.GetUsage(dhRHalfKeyT) == some(u.DhKey(WgDHHK))
	//@ assert iteration > 0 ==> ctx.GetUsage(dhPrivateKeyT) == some(u.DhKey(WgDHSK))
	
	// If iteration > 0, derive newK with KDF from K, dhRHalfKey and the ephemeral key
	/*@
	keyLabel := label.Readers(set[p.Id]{ aPreviousVersId, aVersId, bId })
	ghost if iteration == 0 {
		keyLabel = label.Readers(set[p.Id]{ aSessId, bId })
	}
	@*/

	if iteration == 0 {
		newK = K
		newKT = KT
		//@ assert labeledlib.Mem(newK)
		//@ assert labeledlib.Abs(newK) == tm.gamma(newKT)
		//@ assert ctx.IsAeadKey(t, newKT, keyLabel, WgKir)
		//@ assert ctx.GetUsage(newKT) == some(u.AeadKey(WgKir))
	} else {
		//@ unfold InitiatorMem(initiator)
		dhSharedSecret, err := initiator.llib.DhSharedSecret(dhPrivateKey, dhRHalfKey)
		//@ fold InitiatorMem(initiator)
		//@ ghost dhSharedSecretT := tm.exp(dhRHalfKeyT, dhPrivateKeyT)
		ok = err == nil
		if !ok {
			return
		}
		//@ assert labeledlib.Abs(dhSharedSecret) == tm.gamma(dhSharedSecretT)

		// Verify that `dhSharedSecretT` indeed has a WgDHSS usage
		//@ ProveSharedSecretUsage(ctx, dhRHalfKeyT, dhPrivateKeyT, dhSharedSecretT)
		//@ assert ctx.GetUsage(dhSharedSecretT) == some(u.DhKey(WgDHSS))

		newK = lib.NewByteString(32)
		//@ unfold InitiatorMem(initiator)
		lib.ComputeKDFRatchet(newK, K, dhSharedSecret /*@, currentVersion, versionPerm @*/)
		//@ fold InitiatorMem(initiator)
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
		//@ ProveIsAeadKey(ctx, t, keyLabel, KT, newKT, dhPrivateKeyT, dhSharedSecretT, bId, aVersId, aPreviousVersId, WgKVersIr)
		//@ assert ctx.IsAeadKey(t, newKT, keyLabel, WgKVersIr)
	}

	// Create ephemeral key
	//@ t0 := t
	//@ assert t0 == old(initiator.Snapshot())
	var err error
	//@ unfold InitiatorMem(initiator)
	//@ assert initiator.llib.OwnerWithVersion().Covers(initiator.llib.OwnerWithVersion())
	// The ephemeral key has the current and next versions
	newDhPrivateKey, err /*@, newDhPrivateKeyT @*/ = initiator.llib.GenerateDHKey(/*@ label.Readers(set[p.Id]{ initiator.llib.OwnerWithVersion(), initiator.llib.OwnerWithNextVersion() }), versionPerm, WgDHSK, set[ev.EventType]{ } @*/) // TODO_ add event(s)
	//@ initiator.llib.ApplyMonotonicity()
	//@ fold InitiatorMem(initiator)
	ok = err == nil
	if !ok {
		return
	}
	//@ assert acc(labeledlib.receipt(newDhPrivateKey, currentVersion), versionPerm)
	//@ t = initiator.Snapshot()
	//@ t1 := t
	//@ assert t0.isSuffix(t1)

	// After creating newDhPrivateKey, it should be converted to the next version (when iteration > 0) to allow for a later bump
	//@ unfold InitiatorMem(initiator)
	//@ assert initiator.llib.OwnerWithNextVersion().Covers(initiator.llib.OwnerWithNextVersion())
	//@ initiator.llib.ConvertToNextVersion(newDhPrivateKey, newDhPrivateKeyT, versionPerm)
	//@ fold InitiatorMem(initiator)
	//@ assert acc(labeledlib.receipt(newDhPrivateKey, currentVersion + 1), versionPerm)

	// Obtain the associated public key
	//@ unfold InitiatorMem(initiator)
	dhIHalfKey, err := initiator.llib.DhExp(newDhPrivateKey /*@, newDhPrivateKeyT @*/)
	//@ t = initiator.llib.Snapshot()
	//@ fold InitiatorMem(initiator)
	//@ ghost dhIHalfKeyT := tm.exp(tm.generator(), newDhPrivateKeyT)
	ok = err == nil
	if !ok {
		return
	}
	//@ assert labeledlib.Abs(dhIHalfKey) == tm.gamma(dhIHalfKeyT)
	//@ assert labeledlib.Size(dhIHalfKey) == labeledlib.DHHalfKeyLength

	// Verify that `dhIHalfKeyT` indeed has a WgDHHK usage
	//@ ProveHalfKeyUsage(ctx, dhIHalfKeyT, newDhPrivateKeyT)
	//@ assert ctx.GetUsage(dhIHalfKeyT) == some(u.DhKey(WgDHHK))

	// Delete (old) dhPrivateKey
	if iteration > 0 {
		//@ unfold InitiatorMem(initiator)
		err = initiator.llib.DeleteSafely(dhPrivateKey /*@, versionPerm, versionPerm @*/)
		//@ fold InitiatorMem(initiator)
		ok = err == nil
		if !ok {
			return
		}
	}

	// Delete K
	if iteration > 1 {
		//@ unfold InitiatorMem(initiator)
		err = initiator.llib.DeleteSafely(K /*@, versionPerm, versionPerm @*/)
		//@ fold InitiatorMem(initiator)
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
	//@ unfold InitiatorMem(initiator)
	plaintext := (initiator.LibState).PadMsg(msg)

	//____________ Proving AeadEnc ________________________________
	// TODO_ move (a part of) the proof to a lemma?
	//@ t := initiator.llib.Snapshot()

	//@ assert ctx.IsLabeledRelaxed(t, newKT, keyLabel)
	//@ assert iteration == 0 ==> ctx.IsAeadKey(t, newKT, keyLabel, WgKir)
	//@ assert iteration > 0  ==> ctx.IsAeadKey(t, newKT, keyLabel, WgKVersIr)
	//@ assert exists usageString string :: ctx.IsAeadKey(t, newKT, keyLabel, usageString) // Necessary to prove `CanAeadEncrypt`
	//@ assert ctx.IsPublishable(t, tm.integer64(nonce))
	//@ assert ctx.IsPublishable(t, dhIHalfKeyT)

	//@ assert ctx.IsValid(t, msgT)
	//@ if iteration == 0 {
		//@ assert aSessId.Covers(aSessId)
		//@ assert bId.Covers(bId)
		//@ assert labeling.includesIds(set[p.Id]{ aSessId, bId }, set[p.Id]{ aSessId, bId })
		//@ assert ctx.CanFlow(t, label.Readers(set[p.Id]{ aSessId, bId }), keyLabel)
		//@ ctx.CanFlowTransitive(t, ctx.GetLabel(msgT), label.Readers(set[p.Id]{ aSessId, bId }), keyLabel)
		//@ assert ctx.CanFlow(t, ctx.GetLabel(msgT), keyLabel)
	//@ } else {
		//@ assert bId.Covers(bId)
		//@ assert aSessId.Covers(aPreviousVersId)
		//@ assert aSessId.Covers(aVersId)
		//@ assert labeling.includesIds(set[p.Id]{ aSessId, bId }, set[p.Id]{ aPreviousVersId, aVersId, bId })
		//@ assert ctx.CanFlow(t, label.Readers(set[p.Id]{ aSessId, bId }), label.Readers(set[p.Id]{ aPreviousVersId, aVersId, bId }))
		//@ assert ctx.CanFlow(t, label.Readers(set[p.Id]{ aSessId, bId }), keyLabel)
		//@ ctx.CanFlowTransitive(t, ctx.GetLabel(msgT), label.Readers(set[p.Id]{ aSessId, bId }), keyLabel)
		//@ assert ctx.CanFlow(t, ctx.GetLabel(msgT), keyLabel)
	//@ }
	//@ assert ctx.CanFlow(t, ctx.GetLabel(msgT), keyLabel)
	//@ assert ctx.IsMsg(t, msgT, keyLabel)

	//@ assert exists e tm.Term :: {tm.exp(tm.generator(), e)} dhIHalfKeyT == tm.exp(tm.generator(), e) && e.IsRandom() && GetWgLabeling().GetUsage(dhIHalfKeyT) == some(u.DhKey(WgDHHK)) && t.OnlyNonceOccurs(e)
	//@ assert exists e tm.Term :: {tm.exp(tm.generator(), e)} dhIHalfKeyT == tm.exp(tm.generator(), e) && e.IsRandom() && GetWgLabeling().GetUsage(dhIHalfKeyT) == some(u.DhKey(WgDHHK)) && ctx.GetLabel(e) == label.Readers(set[p.Id]{ aVersId, aNextVersId }) && t.OnlyNonceOccurs(e)
	//@ assert aId.Covers(aVersId)
	//@ assert aId.Covers(aNextVersId)
	//@ assert labeling.includesIds(set[p.Id]{ aId }, set[p.Id]{ aVersId, aNextVersId })
	//@ assert ctx.CanFlow(t, label.Readers(set[p.Id]{ aId }), label.Readers(set[p.Id]{ aVersId, aNextVersId }))
	//@ assert aId == lib.principalId(0)
	//@ assert aId == p.principalId(lib.Principal(0))
	//@ assert ctx.CanFlow(t, label.Readers(set[p.Id]{ p.principalId(lib.Principal(0)) }), label.Readers(set[p.Id]{ aVersId, aNextVersId }))
	//@ assert exists e tm.Term :: {tm.exp(tm.generator(), e)} dhIHalfKeyT == tm.exp(tm.generator(), e) && e.IsRandom() && GetWgLabeling().GetUsage(dhIHalfKeyT) == some(u.DhKey(WgDHHK)) && GetWgLabeling().CanFlow(t, label.Readers(set[p.Id]{ p.principalId(lib.Principal(0)) }), GetWgLabeling().GetLabel(e)) && t.OnlyNonceOccurs(e)

	//@ assert GetWgUsage().versionedIrPayloadPred(t, dhIHalfKeyT)
	//@ assert iteration == 0 ==> GetWgUsage().AeadPred(t, WgKir, newKT, tm.integer64(nonce), msgT, dhIHalfKeyT)
	//@ assert iteration > 0  ==> GetWgUsage().AeadPred(t, WgKVersIr, newKT, tm.integer64(nonce), msgT, dhIHalfKeyT)
	//@ assert (forall usageString string :: ctx.IsAeadKey(t, newKT, keyLabel, usageString) ==> ctx.usage.AeadPred(t, usageString, newKT, tm.integer64(nonce), msgT, dhIHalfKeyT))

	//@ assert ctx.CanAeadEncrypt(t, newKT, tm.integer64(nonce), msgT, dhIHalfKeyT, keyLabel)
	//______________________________________________________________
	encryptedMsg, err := initiator.llib.AeadEnc(newK, nonceBytes, plaintext, dhIHalfKey /*@, newKT, tm.integer64(nonce), msgT, dhIHalfKeyT, keyLabel @*/)
	//@ fold InitiatorMem(initiator)
	ok = err == nil
	if !ok {
		return
	}

	// Construct the message
	message := &lib.Message{
		Type:     4,
		Receiver: conn.RemoteIndex,
		Nonce:    nonce,
		Data:     dhIHalfKey,
		Payload:  encryptedMsg,
	}
	//@ sidR := tm.integer32B(conn.RemoteIndex)
	//@ sidrT := tm.integer32(conn.RemoteIndex)
	packet := lib.MarshalMessage(message)
	//@ packetT := tm.tuple5(tm.integer32(4), sidrT, tm.integer64(nonce), dhIHalfKeyT, tm.aead(newKT, tm.integer64(nonce), msgT, dhIHalfKeyT))
	//@ assert labeledlib.Abs(packet) == tm.gamma(packetT)
	conn.Nonce += 1

	// Prove the message invariant: the packet is publishable
	//@ assert ctx.IsValid(t, tm.integer64(nonce))
	//@ assert ctx.IsValid(t, msgT)
	//@ assert ctx.IsValid(t, dhIHalfKeyT)
	//@ assert ctx.IsValidAead(t, newKT, tm.integer64(nonce), msgT, ctx.GetLabel(msgT), dhIHalfKeyT)
	//@ ctx.IsMsgTupleCreate(t, packetT, label.Public())

	// Send the message
	//@ unfold InitiatorMem(initiator)
	err = initiator.llib.Send(lib.Principal(initiator.a), lib.Principal(initiator.b), packet /*@, packetT @*/)
	ok = err == nil
	//@ initiator.llib.ApplyMonotonicity()
	//@ fold InitiatorMem(initiator)
	//@ t2 := initiator.Snapshot()
	//@ assert t1.isSuffix(t2)

	// Necessary postconditions verification
	//@ assert t0 == old(initiator.Snapshot()) && t0.isSuffix(t1) && t1.isSuffix(t2)
	//@ t0.isSuffixTransitive(t1, t2)
	//@ assert old(initiator.Snapshot()).isSuffix(initiator.Snapshot())
	ghost if iteration == 0 {
		//@ ctx.IsAeadKey(t1, newKT, keyLabel, WgKir)
		//@ ctx.IsValidMonotonic(t1, initiator.Snapshot(), newKT)
		//@ ctx.CanFlowMonotonic(t1, initiator.Snapshot(), label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), ctx.GetLabel(newKT)) 
		//@ assert ctx.IsAeadKey(initiator.Snapshot(), newKT, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), WgKir)
	}
	//@ assert iteration == 0 ==> GetWgLabeling().IsAeadKey(initiator.Snapshot(), newKT, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), WgKir)

	return
}


//@ requires iteration >= 0 && versionPerm > 0 && versionPerm < 1/2
//@ requires InitiatorMem(initiator)
//@ requires unfolding InitiatorMem(initiator) in initiator.llib.Version() == currentVersion
// K properties
//@ requires labeledlib.Mem(K) && labeledlib.Abs(K) == tm.gamma(KT) && labeledlib.Size(K) == 32
//@ requires iteration == 0 ==> GetWgLabeling().IsAeadKey(initiator.Snapshot(), KT, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), WgKri)
//@ requires iteration > 0  ==> GetWgLabeling().IsAeadKey(initiator.Snapshot(), KT, label.Readers(set[p.Id]{ initiator.getAPreviousVersionId(), initiator.getAVersionId(), initiator.getBId() }), WgKVersIr)
//@ requires iteration == 0 ==> GetWgLabeling().CanFlow(initiator.Snapshot(), GetWgLabeling().GetLabel(KT), label.Readers(set[p.Id]{ initiator.getASessId() })) // This is to prove that newK == K is not versioned when decrypting the first message
// dhPrivateKey properties
//@ requires iteration > 0 ==> labeledlib.Mem(dhPrivateKey) && labeledlib.Abs(dhPrivateKey) == tm.gamma(dhPrivateKeyT) && dhPrivateKeyT == tm.random(labeledlib.Abs(dhPrivateKey), label.Readers(set[p.Id]{ initiator.getAVersionId(), initiator.getANextVersionId() }), u.DhKey(WgDHSK)) && GetWgLabeling().IsValid(initiator.Snapshot(), dhPrivateKeyT) && labeledlib.Size(dhPrivateKey) == 32
// dhRHalfKey properties
//@ requires iteration > 0 ==> labeledlib.Mem(dhRHalfKey) && labeledlib.Abs(dhRHalfKey) == tm.gamma(dhRHalfKeyT) // If iteration == 0, the parameter dhRHalfKey is not used
//@ requires iteration > 0 ==> exists e tm.Term :: {tm.exp(tm.generator(), e)} dhRHalfKeyT == tm.exp(tm.generator(), e) && GetWgLabeling().CanFlow(initiator.Snapshot(), label.Readers(set[p.Id]{ initiator.getBId() }), GetWgLabeling().GetLabel(e)) && e.IsRandom() && labeledlib.Size(dhRHalfKey) == labeledlib.DHHalfKeyLength && GetWgLabeling().IsValid(initiator.Snapshot(), dhRHalfKeyT) && GetWgLabeling().GetUsage(dhRHalfKeyT) == some(u.DhKey(WgDHHK))
// guard properties
//@ requires iteration == 0 ==> versionPerm < 1/4 && acc(labeledlib.guard(currentVersion), 1/1) && acc(labeledlib.guardNext(currentVersion+1), 1/1 - versionPerm)
//@ requires iteration > 0  ==> versionPerm < 1/4 && acc(labeledlib.guard(currentVersion), 1/1 - versionPerm) && acc(labeledlib.guardNext(currentVersion+1), 1/1 - versionPerm) && acc(labeledlib.receipt(K, currentVersion), versionPerm)
//@ ensures  InitiatorMem(initiator)
//@ ensures  initiator.ImmutableStateExceptVersion() == old(initiator.ImmutableStateExceptVersion())
//@ ensures initiator.Snapshot() == old(initiator.Snapshot())
//@ ensures  old(initiator.Snapshot()).isSuffix(initiator.Snapshot())
//@ ensures unfolding InitiatorMem(initiator) in ok ==> /*(iteration == 0 ? initiator.llib.Version() == currentVersion :*/ initiator.llib.Version() == currentVersion + 1
// newK properties
//@ ensures  ok ==> labeledlib.Mem(newK) && labeledlib.Abs(newK) == tm.gamma(newKT) && labeledlib.Size(newK) == 32
//@ ensures ok && iteration == 0 ==> GetWgLabeling().IsAeadKey(initiator.Snapshot(), newKT, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), WgKri)
//@ ensures ok && iteration > 0  ==> GetWgLabeling().IsAeadKey(initiator.Snapshot(), newKT, label.Readers(set[p.Id]{ initiator.getAPreviousVersionId(), initiator.getAVersionId(), initiator.getBId() }), WgKVersRi)
// newDhRHalfKey properties
//@ ensures  ok ==> labeledlib.Mem(newDhRHalfKey) && labeledlib.Abs(newDhRHalfKey) == tm.gamma(newDhRHalfKeyT)
//@ ensures  ok ==> exists e tm.Term :: {tm.exp(tm.generator(), e)} newDhRHalfKeyT == tm.exp(tm.generator(), e) && GetWgLabeling().CanFlow(initiator.Snapshot(), label.Readers(set[p.Id]{ initiator.getBId() }), GetWgLabeling().GetLabel(e)) && e.IsRandom() && labeledlib.Size(newDhRHalfKey) == labeledlib.DHHalfKeyLength && GetWgLabeling().IsValid(initiator.Snapshot(), newDhRHalfKeyT) && GetWgLabeling().GetUsage(newDhRHalfKeyT) == some(u.DhKey(WgDHHK))
// dhPrivateKey properties
//@ ensures ok && iteration > 0 ==> labeledlib.Mem(dhPrivateKey) && labeledlib.Abs(dhPrivateKey) == tm.gamma(dhPrivateKeyT) && dhPrivateKeyT == tm.random(labeledlib.Abs(dhPrivateKey), label.Readers(set[p.Id]{ initiator.getAPreviousVersionId(), initiator.getAVersionId() }), u.DhKey(WgDHSK)) && GetWgLabeling().IsValid(initiator.Snapshot(), dhPrivateKeyT) && labeledlib.Size(dhPrivateKey) == 32
// guard properties
//@ ensures  ok && iteration == 0 ==> acc(labeledlib.guard(currentVersion+1), 1/1 - versionPerm) && acc(labeledlib.guardNext(currentVersion+2), 1/1)
//@ ensures  ok && iteration > 0  ==> acc(labeledlib.guard(currentVersion+1), 1/1 - 2*versionPerm) && acc(labeledlib.guardNext(currentVersion+2), 1/1) && acc(labeledlib.receipt(newK, currentVersion+1), versionPerm)
func (initiator *Initiator) receiveMessage(K lib.ByteString, dhPrivateKey lib.ByteString, dhRHalfKey lib.ByteString, conn *lib.Connection, iteration int /*@, ghost KT tm.Term, ghost dhPrivateKeyT tm.Term, ghost dhRHalfKeyT tm.Term, ghost versionPerm perm, ghost currentVersion uint32 @*/) (ok bool , newK lib.ByteString, newDhRHalfKey lib.ByteString /*@, ghost newKT tm.Term, ghost newDhRHalfKeyT tm.Term @*/) {

	// Receive the packet
	//@ unfold acc(InitiatorMem(initiator), 1/8)
	packet, err /*@, term @*/ := initiator.LibState.Receive(lib.Principal(initiator.b), lib.Principal(initiator.a) /*@, initiator.llib.Snapshot() @*/)
	ok = err == nil
	//@ fold acc(InitiatorMem(initiator), 1/8)
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

	//@ unfold acc(InitiatorMem(initiator), 1/8)
	//@ unfold acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), 1/8)
	ok = (initiator.HandshakeInfo).LocalIndex == message.Receiver
	//@ fold acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), 1/8)
	//@ fold acc(InitiatorMem(initiator), 1/8)
	if !ok {
		return
	}

	// Useful constants
	/*@
	ctx := GetWgLabeling()
	t := initiator.Snapshot()
	bId := initiator.getBId()
	aId := initiator.getAId()
	aSessId := initiator.getASessId()
	aVersId := initiator.getAVersionId()
	aNextVersId := initiator.getANextVersionId()
	keyLabel := label.Readers(set[p.Id]{ aVersId, aNextVersId, bId })
	ghost if iteration == 0 {
		keyLabel = label.Readers(set[p.Id]{ aSessId, bId })
	}
	@*/

	// Assume that the obtained term is a 5-tuple 
	/*@
	nonceBytes := lib.NonceToBytes(message.Nonce)

	newDhRHalfKey := message.Data
	newDhRHalfKeyT := tm.oneTerm(labeledlib.Abs(newDhRHalfKey))

	unfold InitiatorMem(initiator)
	initiator.llib.MessageOccursImpliesMessageInv(bId.getPrincipal(), aId.getPrincipal(), term)
	fold InitiatorMem(initiator)
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
		//@ assert ctx.IsAeadKey(t, newKT, keyLabel, WgKri)

		//@ unfold InitiatorMem(initiator)
		plaintext, err = initiator.llib.AeadDec(newK, nonceBytes, message.Payload, newDhRHalfKey /*@, 0/1, newKT, tm.integer64(message.Nonce), predictedPayloadT, newDhRHalfKeyT, keyLabel @*/)
		//@ fold InitiatorMem(initiator)
		ok = err == nil
		if !ok { // ADAPT
			return
		}

		// Proving obtention of `AeadPred`
		//@ m = labeledlib.Abs(plaintext)
		//@ rid := initiator.getRid()
		//@ unfold acc(InitiatorMem(initiator), 1/4)
		//@ fold pap.pattern4Constraints(initiator.llib, bId, WgKri, rid, newKT)
		//@ nonceTX, msgTX, adTX = pap.patternProperty4(initiator.llib, bId, WgKri, rid, newKT, tm.oneTerm(n), tm.oneTerm(m),  tm.oneTerm(a), term)
		//@ unfold pap.pattern4Constraints(initiator.llib, bId, WgKri, rid, newKT)
		//@ fold acc(InitiatorMem(initiator), 1/4)
		//@ assert ctx.IsValidAead(t, newKT, nonceTX, msgTX, ctx.GetLabel(msgTX), adTX)
		//@ assert ctx.IsPublishable(t, newKT) || GetWgUsage().AeadPred(t, u.GetUsageString(get(ctx.GetUsage(newKT))), newKT, nonceTX, msgTX, adTX)
		
	} else {		
		// Obtain the DH shared secret (from the public key given in the associated data, and the private key)
		//@ unfold InitiatorMem(initiator)
		dhSharedSecret, err := initiator.llib.DhSharedSecret(dhPrivateKey, dhRHalfKey)
		//@ ghost dhSharedSecretT := tm.exp(dhRHalfKeyT, dhPrivateKeyT)

		//@ ProveSharedSecretUsage(ctx, dhRHalfKeyT, dhPrivateKeyT, dhSharedSecretT)
		//@ assert ctx.GetUsage(dhSharedSecretT) == some(u.DhKey(WgDHSS))

		//@ fold InitiatorMem(initiator)
		ok = err == nil
		if !ok {
			return
		}
		//@ assert labeledlib.Abs(dhSharedSecret) == tm.expB(labeledlib.Abs(dhRHalfKey), labeledlib.Abs(dhPrivateKey))
		//@ assert labeledlib.Abs(dhSharedSecret) == tm.gamma(dhSharedSecretT)

		// Obtain newK
		newK = lib.NewByteString(32)
		//@ unfold InitiatorMem(initiator)
		lib.ComputeKDFRatchet(newK, K, dhSharedSecret /*@, currentVersion, versionPerm @*/)
		//@ fold InitiatorMem(initiator)
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
		//@ ProveIsAeadKey(ctx, t, keyLabel, KT, newKT, dhPrivateKeyT, dhSharedSecretT, bId, aNextVersId, aVersId, WgKVersRi)
		//@ assert ctx.IsAeadKey(t, newKT, keyLabel, WgKVersRi)

		// After creating newK, it should be converted to the next version (when iteration > 0) to allow for a later bump
		//@ assert exists e tm.Term :: {tm.exp(tm.generator(), e)} ctx.GetLabel(newKT) == label.Join(ctx.GetLabel(e), label.Readers(set[p.Id]{ aVersId, aNextVersId }))
		//@ ProveNewKFlowsToOwnerWithVersion(ctx, t, newKT, bId, aVersId, aNextVersId)
		//@ unfold InitiatorMem(initiator)
		//@ assert ctx.CanFlow(t, ctx.GetLabel(newKT), label.Readers(set[p.Id]{ initiator.llib.OwnerWithNextVersion() }))
		//@ initiator.llib.ConvertToNextVersion(newK, newKT, versionPerm)
		//@ fold InitiatorMem(initiator)
		//@ assert acc(labeledlib.receipt(newK, currentVersion + 1), versionPerm)

		// Delete K
		//@ unfold InitiatorMem(initiator)
		err = initiator.llib.DeleteSafely(K /*@, versionPerm, versionPerm @*/)
		//@ fold InitiatorMem(initiator)
		ok = err == nil
		if !ok {
			return
		}

		// Decrypt the message
		//@ unfold InitiatorMem(initiator)
		plaintext, err = initiator.llib.AeadDec(newK, nonceBytes, message.Payload, newDhRHalfKey /*@, versionPerm, newKT, tm.integer64(message.Nonce), predictedPayloadT, newDhRHalfKeyT, keyLabel @*/)
		//@ fold InitiatorMem(initiator)
		ok = err == nil
		if !ok { // ADAPT
			return
		}

		// Proving obtention of `AeadPred`
		//@ m = labeledlib.Abs(plaintext)
		//@ rid := initiator.getRid()
		//@ unfold acc(InitiatorMem(initiator), 1/4)
		//@ fold pap.pattern4Constraints(initiator.llib, bId, WgKVersRi, rid, newKT)
		//@ nonceTX, msgTX, adTX = pap.patternProperty4(initiator.llib, bId, WgKVersRi, rid, newKT, tm.oneTerm(n), tm.oneTerm(m),  tm.oneTerm(a), term)
		//@ unfold pap.pattern4Constraints(initiator.llib, bId, WgKVersRi, rid, newKT)
		//@ fold acc(InitiatorMem(initiator), 1/4)
		//@ assert ctx.IsValidAead(t, newKT, nonceTX, msgTX, ctx.GetLabel(msgTX), adTX)
		//@ assert ctx.IsPublishable(t, newKT) || GetWgUsage().AeadPred(t, u.GetUsageString(get(ctx.GetUsage(newKT))), newKT, nonceTX, msgTX, adTX)
	}

	//@ assert ctx.IsPublishable(t, newKT) || GetWgUsage().versionedRiPayloadPred(t, adTX)

	// Disjunction of `IsPublishable` and `versionedRiPayloadPred`
	/*@
	ghost if ctx.IsPublishable(t, newKT) {
		// TODO_ do something related to corruption
		ok = false
		return
	}
	
	assert GetWgUsage().versionedRiPayloadPred(t, adTX)
	assert exists e tm.Term :: {tm.exp(tm.generator(), e)} adTX == tm.exp(tm.generator(), e) && e.IsRandom() && GetWgLabeling().GetUsage(adTX) == some(u.DhKey(WgDHHK)) && GetWgLabeling().CanFlow(t, label.Readers(set[p.Id]{ bId }), ctx.GetLabel(e)) && ctx.IsValid(t, adTX)

	assert labeledlib.Mem(message.Data) && labeledlib.Abs(message.Data) == tm.gamma(adTX) && labeledlib.Size(message.Data) == labeledlib.DHHalfKeyLength

	// Write results in returned values
	newDhRHalfKey = message.Data
	newDhRHalfKeyT = adTX
	@*/


	// Delete the message (except the initial one that is not versioned)
	if iteration > 0 {
		// TODO_ should `receiveMessage` return the decrypted message? It is not necessary just for the sake of the protocol. Currently, we delete it right after decryption, but we could add a function call that does something with the message before deleting it.
		//@ unfold InitiatorMem(initiator)
		err = initiator.llib.DeleteSafely(plaintext /*@, versionPerm, versionPerm @*/)
		//@ fold InitiatorMem(initiator)
		ok = err == nil
		if !ok {
			return
		}
	}


	// Bump the version
	//@ unfold InitiatorMem(initiator)
	//@ ghost if iteration == 0 {
		//@ initiator.llib.BumpVersion(1/1 - versionPerm)
	//@ } else {
		//@ initiator.llib.BumpVersion(1/1 - 2*versionPerm)
	//@ }
	//@ fold InitiatorMem(initiator)
	//@ assert unfolding InitiatorMem(initiator) in initiator.llib.Version() == currentVersion + 1
	// //@ assert unfolding InitiatorMem(initiator) in iteration == 0 ? initiator.llib.Version() == currentVersion : initiator.llib.Version() == currentVersion + 1

	// Properties after bumping
	//@ assert iteration == 0 ==> ctx.IsAeadKey(t, newKT, keyLabel, WgKri) // keyLabel is unversioned, so it does not change after the bump
	//@ keyLabelAfterBump := label.Readers(set[p.Id]{ initiator.getAPreviousVersionId(), initiator.getAVersionId(), bId })
	//@ assert iteration > 0  ==> ctx.IsAeadKey(t, newKT, keyLabelAfterBump, WgKVersRi)
	return
}