module main

open signatures
open predicates
open facts
open assertions

pred largeStaticWorld {
	// Snapshot constraint for population analysis.
	#RegisteredUser = 3
	#Trip = 4
	#Path = 5
	#Segment = 6
	#visibility.Public >= 2
	#currentStatus.Dangerous >= 1
}

// Static World
run largeStaticWorld for 10 

pred dynamicWorld {	
	// Step 1: Initialization and first sign up.
	(initialize and signUp) 
	
	// Step 2: User 1 records a trip.
	and after (
		(some u: RegisteredUser | recordTrip[u, Optimal, Sunny])
		
		// Step 3: User 2 signs up.
		and after (
			signUp
			
			// Step 4: User 2 creates a manual path.
			and after (
				(some u: RegisteredUser | #u.paths = 0 and createManualPath[u, Dangerous])
				
				// Step 5: User 1 publishes their path.
				and after (
					(some u: RegisteredUser, p: Path | p.userRating = Optimal and publishPath[u, p])

					// Step 6: User 3 signs up.
					and after (
						signUp

						// Step 7: User 3 records a trip.
						and after (
							(some u: RegisteredUser | #u.paths = 0 and recordTrip[u, NeedsMaintenance, Cloudy])

							// Step 8: User 2 publishes their path.
							and after (
								(some u: RegisteredUser, p: Path | p.userRating = Dangerous and publishPath[u, p])
								
								// Step 9: User 3 publishes their path.
								and after (
									(some u: RegisteredUser, p: Path | p.userRating = NeedsMaintenance and publishPath[u, p])
							)
							)
						)
					)
				)
			)
		)
	)
}

// Dynamyc World
run dynamicWorld for 5 but 15 Segment

// Verification Commands
check VisibilityIsolation for 5
check SegmentsStatusSync for 5
check OncePublicAlwaysPublic for 5
check SharingIsImpossible for 5
