package principal

type Principal = string

/*@
type Id domain {
	// constructors
	// type 0
	func principalId(Principal) Id
	// type 1
	func sessionId(Principal, uint32) Id
	// type 2
	func versionId(Principal, uint32, uint32) Id // Version

	// deconstructors
	func getIdType(Id) int
	func getIdPrincipal(Id) Principal
	func getIdSession(Id) uint32
	func getIdVersion(Id) uint32

	// WARNING: adapt first axiom if another Id is added!

    axiom { // every Id belongs to a known type
        forall id Id :: { getIdType(id) } 0 <= getIdType(id) && getIdType(id) <= 3
    }

	axiom { // principalId is injective
		forall principal Principal :: { principalId(principal) } getIdType(principalId(principal)) == 0 &&
			getIdPrincipal(principalId(principal)) == principal
	}
	axiom { // principalId implies its constructions
        forall id Id :: { getIdType(id) } getIdType(id) == 0 ==>
            id == principalId(getIdPrincipal(id))
    }

	axiom { // sessionId is injective
		forall principal Principal, session uint32 :: { sessionId(principal, session) } getIdType(sessionId(principal, session)) == 1 &&
			getIdPrincipal(sessionId(principal, session)) == principal &&
			getIdSession(sessionId(principal, session)) == session
	}
	axiom { // sessionId implies its constructions
        forall id Id :: { getIdType(id) } getIdType(id) == 1 ==>
            id == sessionId(getIdPrincipal(id), getIdSession(id))
    }

	axiom { // versionId is injective
		forall principal Principal, session, version uint32 :: { versionId(principal, session, version) } getIdType(versionId(principal, session, version)) == 2 &&
			getIdPrincipal(versionId(principal, session, version)) == principal &&
			getIdSession(versionId(principal, session, version)) == session &&
			getIdVersion(versionId(principal, session, version)) == version
	}
	axiom { // versionId implies its constructions
        forall id Id :: { getIdType(id) } getIdType(id) == 2 ==>
            id == versionId(getIdPrincipal(id), getIdSession(id), getIdVersion(id))
    }
}

// TODO this should be ghost
decreases
ensures res == principalId(principal)
pure func NewPrincipalId(principal Principal) (res Id)

// TODO this should be ghost
decreases
ensures res == sessionId(principal, session)
pure func NewSessionId(principal Principal, session uint32) (res Id)

// TODO this should be ghost
decreases
ensures res == versionId(principal, session, version)
pure func NewVersionId(principal Principal, session uint32, version uint32) (res Id)

ghost
decreases
pure func (id Id) IsPrincipal() bool {
	return getIdType(id) == 0
}

ghost
decreases
pure func (id Id) IsSession() bool {
	return getIdType(id) == 1
}

ghost
decreases
pure func (id Id) IsVersion() bool {
	return getIdType(id) == 3
}

ghost
decreases
pure func (id Id) getPrincipal() Principal {
	return getIdPrincipal(id)
}

ghost
decreases
pure func (id Id) getSession() option[uint32] {
	return id.IsPrincipal() ? none[uint32] :
		some(getIdSession(id))
}

ghost
decreases
pure func (id Id) getPrincipalId() Id {
	return principalId(id.getPrincipal())
}

ghost
decreases
// returns true iff `id1` covers `id2` meaning that versions covered by `id1`
// is equal or a superset of the versions covered by `id2`
pure func (id1 Id) Covers(id2 Id) bool {
	return id1.IsPrincipal() ? (id1.getPrincipal() == id2.getPrincipal()) :
		id1.IsSession() ? (id1.getPrincipal() == id2.getPrincipal() &&
			id1.getSession() == id2.getSession()) :
		id1 == id2 // if id1 is a version
}

ghost
decreases
ensures id1.Covers(id1)
func (id1 Id) CoversReflexive() {
	// no body needed
}

ghost
decreases
requires id1.Covers(id2) && id2.Covers(id3)
ensures  id1.Covers(id3)
func (id1 Id) CoversTransitive(id2, id3 Id) {
	// no body needed
}

ghost
decreases
ensures id.getPrincipalId().Covers(id)
func (id Id) CoveredByPrincipal() {
	// no body needed
}
@*/
