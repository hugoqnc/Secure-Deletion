package common

import fmt "fmt"
import p "github.com/ModularVerification/ReusableVerificationLibrary/principal"

// TODO_ This was previously in package `library`. Because we need this function in common, we moved it here. Otherwise, we couldn't import the library in common because of a circular dependency. Is it acceptable?
// we perform an injective uint32 to string conversion
//@ trusted
//@ decreases _
//@ ensures forall id2 uint32 :: id != id2 ==> res != Principal(id2)
//@ pure
func Principal(id uint32) (res p.Principal) {
	return fmt.Sprint(id)
}