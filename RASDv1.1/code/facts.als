module facts

open signatures
open predicates

fact StructuralRules {
	always {
		// Integrity: No orphaned segments.
		all s: Segment | s in Path.segments
		
		// Uniqueness: Trip-Path injection.
		all disj t1, t2: Trip | t1.path != t2.path
	}
}

fact OwnershipRules {
	always {
		// Bi-directional consistency between Users, Paths, and Trips.
		all p: Path | one u: RegisteredUser | p in u.paths
		all t: Trip | one u: RegisteredUser | t in u.trips
		
		// Transitive consistency.
		all u: RegisteredUser, t: u.trips | t.path in u.paths
	}
}

fact NewSegmentsMustBeUnknown {
	always {
		// Initialization rule for disjoint new atoms.
		all s: Segment' - Segment | s.currentStatus' = Unknown
	}
}

fact SystemTrace {
	// Linear Temporal Logic definition of valid traces.
	always {
		initialize 
		or doNothing 
		or signUp 
		or (some u: RegisteredUser, s: Status, w: Weather | recordTrip[u, s, w])
		or (some u: RegisteredUser, s: Status | createManualPath[u, s])
		or (some u: RegisteredUser, p: Path | publishPath[u, p])
	}
}

fact ConsistentTrips {
	always {
		// Internal fields are immutable.
		all t: Trip | t.path' = t.path
		all t: Trip | t.weather' = t.weather
		
		// Set stability. Trips can be added only through recordTrip[]
		Trip' != Trip implies (some u: RegisteredUser, s: Status, w: Weather | recordTrip[u, s, w])
	}
}

fact ConsistentPaths {
	always {
		// Structure and Rating are immutable.
		all p: Path | p.segments' = p.segments
		all p: Path | p.userRating' = p.userRating and p.userRating != Unknown
		
		// Visibility changes only via publishPath.
		all p: Path | 
			p.visibility' != p.visibility 
			implies (some u: RegisteredUser | publishPath[u, p]) 
		
		// Set stability. Paths can be added only through recordTrip[] or createManualPath[]
		Path' != Path implies (
			(some u: RegisteredUser, st: Status, w: Weather | recordTrip[u, st, w]) or
			(some u: RegisteredUser, st: Status | createManualPath[u, st])
		)
	}
}

fact ConsistentSegments {
	always {
		// State transition: Segment status synchronizes with Path rating upon publication.
		all s: Segment | 
			(s.currentStatus' != s.currentStatus) 
			implies (some u: RegisteredUser, p: Path | publishPath[u, p] and s in p.segments and s.currentStatus' = p.userRating)
		
		// Set stability. Segments can be added only through recordTrip[] or createManualPath[]
		Segment' != Segment implies (
			(some u: RegisteredUser, st: Status, w: Weather | recordTrip[u, st, w]) or
			(some u: RegisteredUser, st: Status | createManualPath[u, st])
		)
	}
}

fact ConsistentRegisteredUsers {
	always {
		// User relations update only via specific actions.
		all u: RegisteredUser | u.trips' != u.trips 
			implies (some s: Status, w: Weather | recordTrip[u, s, w]) 

		all u: RegisteredUser | u.paths' != u.paths 
			implies (
				(some s: Status, w: Weather | recordTrip[u, s, w])  or 
				(some s: Status | createManualPath[u, s])
			) 
		// Set stability. Users can be added only through signUp[]
		RegisteredUser' != RegisteredUser implies signUp[]
	}
}
