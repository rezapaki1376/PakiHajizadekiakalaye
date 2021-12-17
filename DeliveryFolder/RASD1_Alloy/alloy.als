// Signatures

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

sig PolicyMaker extends User {}

sig Farmer extends User {
	farm: one Farm,
	performance: one Int
}
{ performance >=0 and performance <= 1 }

sig Farm {
	location: one Location,
	products:some Product
}

sig Location {
	latitude: one Int,
	longitude: one Int
}
{ latitude >= -90 and latitude <= 90 and longitude >= -180 and longitude <= 180 }

sig Product {
	type: one Type,
	producedAmount: one Int
}

sig Type {}

sig Problem {
	description: one String
}

sig DiscussionForum {
	title: one String,
	messages: some Message
}

sig Message {}

sig Suggestion {
	description: one String
}

// Facts

// every email must be associated to just one user
fact EmailAssociationUser {
	all e: Email | one u: User | e in u.email
}

// every password must be associated to at least one user
fact PasswordAssociationUser {
	all p: Password | some u: User | p in u.password
}

// every firstname must be associated to at least one user
fact FirstnameAssociationUser {
	all fn: Firstname | some u: User | fn in u.firstname
}

// every lastname must be associated to at least one user
fact LastnameAssociationUser {
	all ln: Lastname | some u: User | ln in u.lastname
}

// every type of product must be associated to at least one user
fact TypeAssociationProduct {
	all t: Type | some p: Product | t in p.type
}

// every message must be associated to at least one discussion forum
fact MessageAssociationDiscussionForum {
	all m: Message | some df: DiscussionForum | m in df.messages
}


pred show {
	#User >= 2
}

