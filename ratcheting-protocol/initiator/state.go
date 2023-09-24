package initiator

import lib "github.com/ModularVerification/casestudies/wireguard/library"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/common"

import ll "github.com/ModularVerification/ReusableVerificationLibrary/labeledlibrary"
//@ import labeledlib "github.com/ModularVerification/ReusableVerificationLibrary/labeledlibrary/library"
//@ import p "github.com/ModularVerification/ReusableVerificationLibrary/principal"
//@ import tm "github.com/ModularVerification/ReusableVerificationLibrary/term"
//@ import tr "github.com/ModularVerification/ReusableVerificationLibrary/trace"


type Initiator struct {
	LibState      lib.LibraryState
	HandshakeInfo lib.HandshakeArguments
	a, b          uint32
	llib 		  *ll.LabeledLibrary // added
}

/*@
const WgSendingKey = "WG kir Key"
const WgReceivingKey = "WG kri Key"

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) getRid() (rid tm.Term) {
	return unfolding acc(InitiatorMem(initiator), _) in unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in (
		tm.integer32((initiator.HandshakeInfo).LocalIndex))
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) getPP() (pp tm.Term) {
	return unfolding acc(InitiatorMem(initiator), _) in tm.tuple4(tm.integer32(initiator.a), tm.integer32(initiator.b), tm.prologueTerm(), tm.infoTerm())
}

pred HandshakeMem(hs *lib.Handshake) {
	acc(hs) && labeledlib.Mem(hs.ChainHash) && labeledlib.Mem(hs.ChainKey) && labeledlib.Mem(hs.LocalEphemeral) &&
	labeledlib.Size(hs.ChainHash) == 32 && labeledlib.Size(hs.ChainKey) == 32 && labeledlib.Size(hs.LocalEphemeral) == 32
}

ghost
requires acc(HandshakeMem(hs), _)
pure func getNHash(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem(hs), _) in labeledlib.Abs(hs.ChainHash)
}

ghost
requires acc(HandshakeMem(hs), _)
pure func getNKey(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem(hs), _) in labeledlib.Abs(hs.ChainKey)
}

ghost
requires acc(HandshakeMem(hs), _)
pure func getEkI(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem(hs), _) in labeledlib.Abs(hs.LocalEphemeral)
}

ghost
requires acc(HandshakeMem(hs), _)
pure func getSidR(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem(hs), _) in tm.integer32B(hs.RemoteIndex)
}


pred InitiatorMem(initiator *Initiator) {
	lib.LibMem(&initiator.LibState) &&
	lib.HandshakeArgsMem(&initiator.HandshakeInfo) &&
	acc(&initiator.a) && acc(&initiator.b) &&
	initiator.a == 0 && initiator.b == 1 &&
	acc(&initiator.llib) &&
	initiator.llib.Mem() &&
	initiator.llib.Ctx() == GetWgContext() &&
	initiator.llib.LabelCtx() == GetWgLabeling() &&
	unfolding lib.HandshakeArgsMem(&initiator.HandshakeInfo) in
		initiator.llib.Owner() == p.sessionId(lib.Principal(initiator.a), initiator.HandshakeInfo.LocalIndex)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func getSidI(initiator *Initiator) tm.Bytes {
	return unfolding acc(InitiatorMem(initiator), _) in unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in tm.integer32B((initiator.HandshakeInfo).LocalIndex)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func getKI(initiator *Initiator) tm.Bytes {
	return unfolding acc(InitiatorMem(initiator), _) in unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in labeledlib.Abs((initiator.HandshakeInfo).PrivateKey)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func getPkR(initiator *Initiator) tm.Bytes {
	return unfolding acc(InitiatorMem(initiator), _) in unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in labeledlib.Abs((initiator.HandshakeInfo).RemoteStatic)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func getPsk(initiator *Initiator) tm.Bytes {
	return unfolding acc(InitiatorMem(initiator), _) in unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in labeledlib.Abs((initiator.HandshakeInfo).PresharedKey)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) Snapshot() tr.TraceEntry {
	return unfolding acc(InitiatorMem(initiator), _) in initiator.llib.Snapshot()
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) getAId() p.Id {
	return unfolding acc(InitiatorMem(initiator), _) in lib.principalId(initiator.a)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) getASessId() p.Id {
	return p.sessionId(initiator.getAId().getPrincipal(), tm.getInt32(initiator.getRid()))
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) getAVersionId() p.Id {
	return unfolding acc(InitiatorMem(initiator), _) in p.versionId(initiator.getAId().getPrincipal(), tm.getInt32(initiator.getRid()), initiator.llib.Version())
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) getANextVersionId() p.Id {
	return unfolding acc(InitiatorMem(initiator), _) in p.versionId(initiator.getAId().getPrincipal(), tm.getInt32(initiator.getRid()), initiator.llib.Version() + 1)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) getAPreviousVersionId() p.Id {
	return unfolding acc(InitiatorMem(initiator), _) in p.versionId(initiator.getAId().getPrincipal(), tm.getInt32(initiator.getRid()), initiator.llib.Version() - 1)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) getBId() p.Id {
	return unfolding acc(InitiatorMem(initiator), _) in lib.principalId(initiator.b)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) getBSessId(bSess uint32) p.Id {
	return p.sessionId(initiator.getBId().getPrincipal(), bSess)
}

type ImmutableState struct {
	a, b, rid uint32
	llib ll.ImmutableState
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) ImmutableState() ImmutableState {
	return unfolding acc(InitiatorMem(initiator), _) in
		unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in
			ImmutableState{ initiator.a, initiator.b, initiator.HandshakeInfo.LocalIndex, initiator.llib.ImmutableState() }
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) ImmutableStateExceptVersion() ImmutableState {
	return unfolding acc(InitiatorMem(initiator), _) in
		unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in
			ImmutableState{ initiator.a, initiator.b, initiator.HandshakeInfo.LocalIndex, initiator.llib.ImmutableStateExceptVersion() }
}
@*/
