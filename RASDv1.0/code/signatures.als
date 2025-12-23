module signatures

// Simplified enumerations that emulate the different statuses
enum Visibility { Private, Public }
enum Status { Optimal, NeedsMaintenance, Dangerous, Unknown }
enum Weather { Sunny, Cloudy, Rainy }

// Segments have a status that is influenced by the publication of Paths
var sig Segment {
	var currentStatus: Status
}

// Guests are not represented in the Model as their role is to view data
// Each User has a set of Trips and Paths that can grow over time
var sig RegisteredUser {
	var trips: set Trip,
	var paths: set Path
}

// Paths have at leat one Segment, a status and a visibility. Their visibility affects Segment status
var sig Path {
	var segments: some Segment,
	var status: one Status,
	var visibility: Visibility
}

// A Trip is associated with exactly one Path
var sig Trip {
	var path: one Path,
	var weather: lone Weather
}
