module assertions

open signatures
open predicates

assert VisibilityIsolation {
	// Verifies that publishing a path does not unintentionally alter the visibility of disjoint paths.
	always {
		all u: RegisteredUser, p: Path | 
		publishPath[u, p] implies (all otherP: Path - p | otherP.visibility' = otherP.visibility)
	}
}

assert SegmentsStatusSync {
	// Verifies that segment status changes are strictly causal to path publication.
	always {
		all s: Segment |
		s.currentStatus' != s.currentStatus implies 
		(some u: RegisteredUser, p: Path | publishPath[u, p] and s in p.segments)
	}
}

assert OncePublicAlwaysPublic {
	// Verifies that public visibility is an absorbing state.
	always {
		all p: Path | p.visibility = Public implies always (p.visibility = Public)
	}
}

assert SharingIsImpossible {
	// Asserting that segments can NEVER be shared.
	// A counterexample found by the solver proves that segment sharing IS possible.
	always {
		all disj p1, p2: Path | no (p1.segments & p2.segments)
	}
}
