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
	creates: set DiscussionForum,
	gives: set Suggestion,
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
	title: one String,
	messages: set Message
}

sig Type {}

sig Problem {}

sig Message {}

sig Suggestion {}

sig Map {}

////////// FACTS //////////

// each email must be associated to just one user
fact EmailAssociationUser {
	all e: Email | one u: User | e in u.email
}

// each password must be associated to at least one user
fact PasswordAssociationUser {
	all p: Password | some u: User | p in u.password
}

// each firstname must be associated to at least one user
fact FirstnameAssociationUser {
	all fn: Firstname | some u: User | fn in u.firstname
}

// each lastname must be associated to at least one user
fact LastnameAssociationUser {
	all ln: Lastname | some u: User | ln in u.lastname
}

// each farm must have only one farmer as owener
fact FarmOwenershipFarmer {
	all farm: Farm | one farmer: Farmer | farm in farmer.owes
}

// each location must be associated to only one farm
fact LocationAssociationFarm {
	all l: Location | one f: Farm | l in f.locatedOn
}

// each product must has grown in at least a farm
fact ProductAssociationFarm {
	all p: Product | some f: Farm | p in f.products
}

// each type of product must be associated to at least one product
fact TypeAssociationProduct {
	all t: Type | some p: Product | t in p.type
}

// each problem must be created by at least one farmer
fact CreateProblemByFarmer {
	all p: Problem | some f: Farmer | p in f.faces
}

// each suggestion must be given by at least one farmer
fact GiveSuggestionByFarmer {
	all s: Suggestion | some f: Farmer | s in f.gives
}

// each message must be associated to at least one discussion forum
fact MessageAssociationDiscussionForum {
	all m: Message | some df: DiscussionForum | m in df.messages
}

pred show {
	#Farmer >= 2
	#PolicyMaker > 0
	#Problem > 0
	#Suggestion >0
}

run show

