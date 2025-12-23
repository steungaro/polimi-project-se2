module predicates

open signatures

pred initialize {
	// For initial setup
	no RegisteredUser
	no Trip
	no Path
	no Segment
}

pred doNothing {
	// Does nothing
}

pred signUp {
	// Transition: Introduces a new RegisteredUser atom.
	// Post-condition: New user has empty relation sets.
	some newUser: RegisteredUser' - RegisteredUser | {
		RegisteredUser' = RegisteredUser + newUser
		no newUser.trips'
		no newUser.paths'
	}
}

pred recordTrip [u: RegisteredUser, st: Status, w: Weather] {
	// Pre-condition: User is registered.
	u in RegisteredUser
	
	some recordTrip: Trip' - Trip, newPath: Path' - Path | {
		// Universe expansion
		Trip' = Trip + recordTrip
		Path' = Path + newPath
		Segment in Segment' 
		
		let newSegs = Segment' - Segment {
			// New segments are strictly included in the new path.
			newSegs in newPath.segments'
			
			// Dynamic expansion: At least 1 new segment must be created.
			#newSegs >= 1
			
			// Complexity constraint: Path must consist of at least 2 segments.
			#newPath.segments' >= 2
			
			// Property assignment
			recordTrip.path' = newPath
			recordTrip.weather' = w
			newPath.userRating' = st
			newPath.visibility' = Private
			
			// Relation updates
			trips' = trips + (u -> recordTrip)
			paths' = paths + (u -> newPath)
			
			// New segments default to Unknown status.
			currentStatus' = currentStatus + (newSegs -> Unknown)
		}
	}
}

pred createManualPath [u: RegisteredUser, st: Status] {
	// Pre-condition: User is registered.
	u in RegisteredUser
	
	some newPath: Path' - Path | {
		// Universe expansion
		Path' = Path + newPath
		Trip' = Trip 
		Segment in Segment' 
		
		let newSegs = Segment' - Segment {
			// New segments are strictly included in the new path.
			newSegs in newPath.segments'
			
			// Dynamic expansion: At least 1 new segment must be created.
			#newSegs >= 1
			
			// Complexity constraint: Path must consist of at least 2 segments.
			#newPath.segments' >= 2
			
			// Property assignment
			newPath.segments' = newSegs
			newPath.userRating' = st
			newPath.visibility' = Private
			
			// Relation updates
			paths' = paths + (u -> newPath)
			currentStatus' = currentStatus + (newSegs -> Unknown)
		}
	}
}

pred publishPath [u: RegisteredUser, p: Path] {
	// Pre-conditions
	u in RegisteredUser
	p in u.paths 
	p.visibility = Private 
	
	// Target path visibility becomes Public.
	p.visibility' = Public

	// Visibility of all other paths remains invariant.
	all otherP: Path - p | otherP.visibility' = otherP.visibility

	// Segments update logic.
	currentStatus' = currentStatus ++ (p.segments -> p.userRating)
}
