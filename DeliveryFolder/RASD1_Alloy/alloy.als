////////// SIGNATURES //////////

sig Email {}

sig Password {}

sig Firstname {}

sig Lastname {}

abstract sig User {
	email: one Email,
	password: one Password,
	firstname: one Firstname,
	lastname: one Lastname
}

sig PolicyMaker extends User {
	labels: some Farmer
}

sig Farmer extends User {
	performance: one Int,
	owes: one Farm,
	faces: set Problem,
	views: set Map
}{
	performance >= 0
	performance =< 5
}
/* we defined the performance range from 0 to 5, for simplicity!
because alloy Int range is from -8 to 7
*/

sig Farm {
	locatedOn: one Location,
	products: some Product
}

sig Location {
	latitude: one Int,
	longitude: one Int
}{
	latitude >= -5 and latitude =< 5
	longitude >= -5 and longitude =< 5
}
/* we defined the latitude and longitude range from -5 to 5, for simplicity!
because alloy Int range is from -8 to 7
in fact, latitude range is from -90 to 90 and longitude range is from -180 to 180
*/

sig Product {
	type: one Type,
	producedAmount: one Int
}{
	producedAmount > 0
}

sig DiscussionForum {
	creator: one Farmer,
	title: one Title,
	messages: some Message
}

sig Suggestion {
	sender: one Farmer,
	receiver: one Farmer,
	solves: one Problem
}

sig Type {}

sig Problem {}

sig Message {}

sig Title {}

sig Map {}

////////// FACTS //////////

// each email always must be associated with only one user
fact EmailAssociationUser {
	all e: Email | one u: User | e in u.email
}

// each password always must be associated with at least one user
fact PasswordAssociationUser {
	all p: Password | some u: User | p in u.password
}

// each firstname always must be associated with at least one user
fact FirstnameAssociationUser {
	all fn: Firstname | some u: User | fn in u.firstname
}

// each lastname always must be associated with at least one user
fact LastnameAssociationUser {
	all ln: Lastname | some u: User | ln in u.lastname
}

// each farm always must have only one farmer as owener
fact FarmOwenershipFarmer {
	all farm: Farm | one farmer: Farmer | farm in farmer.owes
}

// each location always must be associated with only one farm
fact LocationAssociationFarm {
	all l: Location | one f: Farm | l in f.locatedOn
}

// each location must refer to a different place
fact {
	all disj l1, l2: Location |
	l1.latitude = l2.latitude => l1.longitude != l2.longitude
}

// each product always must be associated with at least a farm
fact ProductAssociationFarm {
	all p: Product | some f: Farm | p in f.products
}

// each type of product always must be associated with at least one product
fact TypeAssociationProduct {
	all t: Type | some p: Product | t in p.type
}

// A farm shouln't have two product with same type
fact DifferentProductType {
	all f: Farm | all disj p1, p2: Product |
	p1 in f.products and p2 in f.products => p1.type != p2.type
}

// each problem always must be associated with at least one farmer
fact ProblemAssociationFarmer {
	all p: Problem | some f: Farmer | p in f.faces
}

// sender and receiver of a suggestion must be different
fact DistinctSenderReceiver {
	all s: Suggestion | s.sender != s.receiver
}

// sender of a suggestion shouldn't be someone who faces the same problem
fact SuggestionSenderLimitation {
	all f: Farmer, s: Suggestion |
	s.solves in f.faces => f != s.sender
}

// receiver of a suggestion must be someone who faces the problem
fact SuggestionReceiverLimitation {
	all f: Farmer, s: Suggestion |
	f = s.receiver => s.solves in f.faces
}

// each message always must be associated with at least one discussion forum
fact MessageAssociationDiscussionForum {
	all m: Message | some df: DiscussionForum | m in df.messages
}

// each title always must be associated with at least one discussion forum
fact TitleAssociationDiscussionForum {
	all t: Title | some df: DiscussionForum | t in df.title
}

// a farmer shouldn't create two discussion forum with same title
fact DifferentDiscussionForumTitle {
	all f: Farmer | all disj df1, df2: DiscussionForum |
	f = df1.creator and f = df2.creator => df1.title != df2.title
}


pred show {
	#Farmer > 1
	#PolicyMaker > 0
	#Problem > 1
	#Suggestion > 1
	#DiscussionForum > 1
	#Map = 2
	#Product > 3
}

run show for 10

