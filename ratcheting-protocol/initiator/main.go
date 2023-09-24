package initiator

//@ import "github.com/ModularVerification/ReusableVerificationLibrary/label"
import ll "github.com/ModularVerification/ReusableVerificationLibrary/labeledlibrary"
//@ import labeledlib "github.com/ModularVerification/ReusableVerificationLibrary/labeledlibrary/library"
//@ import "github.com/ModularVerification/ReusableVerificationLibrary/labeling"
//@ import p "github.com/ModularVerification/ReusableVerificationLibrary/principal"
//@ import tm "github.com/ModularVerification/ReusableVerificationLibrary/term"

import lib "github.com/ModularVerification/casestudies/wireguard/library"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/common"


// to retain a similar code structure, the parameters passed to the implementation (such as its secret key or the peer's public key)
// are not directly parameters to this function but are returned by `getInitialState`
//@ requires lib.LibMem(&initiator.LibState) && acc(&initiator.HandshakeInfo) && acc(&initiator.a) && acc(&initiator.b) && acc(&initiator.llib)
//@ requires a == 0 && b == 1
//@ requires llib.Mem() && llib.Ctx() == GetWgContext() && llib.LabelCtx() == GetWgLabeling() && llib.Owner() == p.sessionId(lib.Principal(a), sid) && llib.Version() == 0
//@ requires labeledlib.guard(0) && labeledlib.guardNext(1)
func (initiator *Initiator) RunInitiator(sid, a, b uint32, llib *ll.LabeledLibrary) {
	ok /*@, pskT, ltkT, ltpkT @*/ := initiator.getInitialState(sid, a, b, llib)
	if !ok {
		return
	}
	
	//@ ghost var corrupted bool
	//@ ghost var bSess uint32
	//@ ghost var ekiT, epkRX, ekRX, kirT, kriT tm.Term
	keypair, ok /*@, corrupted, bSess, ekiT, epkRX, ekRX, kirT, kriT @*/ := initiator.runHandshake( /*@ pskT, ltkT, ltpkT @*/ )
	if !ok {
		return
	}

	go initiator.forwardPackets(keypair /*@, ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted @*/)
}

//@ requires lib.LibMem(&initiator.LibState) && acc(&initiator.HandshakeInfo) && acc(&initiator.a) && acc(&initiator.b) && acc(&initiator.llib)
//@ requires a == 0 && b == 1
//@ requires llib.Mem() && llib.Ctx() == GetWgContext() && llib.LabelCtx() == GetWgLabeling() && llib.Owner() == p.sessionId(lib.Principal(a), sid) && llib.Version() == 0
//@ ensures  ok ==> InitiatorMem(initiator)
//@ ensures  ok ==> unfolding InitiatorMem(initiator) in initiator.llib.Version() == 0 // TODO_ is there something more generic than just specifying the version? 
//@ ensures  ok ==> getPsk(initiator) == tm.gamma(pskT)
//@ ensures  ok ==> getKI(initiator) == tm.gamma(ltkT)
//@ ensures  ok ==> getPkR(initiator) == tm.gamma(ltpkT)
//@ ensures  ok ==> GetWgLabeling().IsLabeled(initiator.Snapshot(), pskT, label.Public())
//@ ensures  ok ==> GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getAId(), ltkT, labeling.KeyTypeDh(), WgKey)
//@ ensures  ok ==> ltkT.IsRandom()
//@ ensures  ok ==> GetWgLabeling().IsPublicKeyExistential(initiator.Snapshot(), initiator.getBId(), ltpkT, labeling.KeyTypeDh(), WgKey)
func (initiator *Initiator) getInitialState(sid, a, b uint32, llib *ll.LabeledLibrary) (ok bool /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term @*/) {

	var psk lib.ByteString
	ok, psk /*@, pskT @*/ = initiator.LibState.GetPsKBio(a, b /*@, llib @*/)
	if !ok || len(psk) != 32 {
		ok = false
		return
	}

	var ltk lib.ByteString
	ok, ltk /*@, ltkT @*/ = initiator.LibState.GetLtKBio(a /*@, llib @*/)
	if !ok || len(ltk) != 32 {
		ok = false
		return
	}

	var ltpk lib.ByteString
	ok, ltpk /*@, ltpkT @*/ = initiator.LibState.GetLtpKBio(b /*@, llib @*/)
	if !ok || len(ltpk) != 32 {
		ok = false
		return
	}

	initiator.HandshakeInfo.PresharedKey = psk
	initiator.HandshakeInfo.PrivateKey = ltk
	initiator.HandshakeInfo.LocalIndex = sid
	initiator.HandshakeInfo.LocalStatic = lib.PublicKey(ltk)
	initiator.HandshakeInfo.RemoteStatic = ltpk
	initiator.a = a
	initiator.b = b
	initiator.llib = llib

	//@ fold lib.HandshakeArgsMem(&initiator.HandshakeInfo)
	//@ fold InitiatorMem(initiator)
	return
}
