sig Strings{}

sig Time{
	minutes: one Int,
	hours: one Int
}

sig CurrentTime extends Time{}

abstract sig Bool{}


sig True extends Bool{}
sig False extends Bool{}

sig Position{}

sig Guest{}

sig User{

	name: one String,
	surname: one String,
	age: one Int,
	email: one String,
	phoneNumber: one String,
	username: one String,
	password: one String,
	licenseNumber: one String
}

sig Driver extends User{
	reqNumber: one String
} 

sig Request{
	reqNumber: one String, 	
	driverId: one String,
	start: Time,
	car: Car,
	pos: Position
}

sig Travel{
 	reqNumber: one String,
	car: Car,
	driverId: String,
	passengers: one Int
}

sig FinishedTravel extends Travel{
	normalFee: one Int,
	leftSpecialParking: one Bool,
	plugged: one Bool,
	discounts: Discounts,
	penalty: Penalty,
	finalFee: one Int
}


  
sig Passenger{}


sig Charge{
	batteryLevel: one Int
}

sig Car{
	isAvailable: one Bool,
	plateNumber: one String,
	model: one String,
	engineSize: one Int,
	seats: one Int,
	charge: Charge
}

sig Discounts{
 	passengersDiscount: one Int,
	batteryDiscount: one Int,
	plugDiscount: one Int
}

sig Penalty{
	distancePenalty: one Int
}


// There aren't users with the same username
fact noDuplicateUsername{
no u1,u2 : User | u1.username = u2.username
}

//There aren't people with 2 accounts
fact noDuplicateUser{
no u1,u2: User | u1.name = u2.name && u1.surname=u2.surname
}

//Every user is an adult
fact noMinors{
no u:User | u.age < 18
}

// The number of passengers can't exceed the number of seats
fact noTooManyPassenger{
 all t:Travel | t.passengers <= t.car.seats
}


// There aren't cars with the same plate number
fact noDuplicateCars{
no c1,c2:Car | c1.plateNumber = c2.plateNumber
}

// The user has done the request is also the only who drives the car
fact uniqueDriverForARequest{
no t:Travel, r:Request| t.reqNumber = r.reqNumber && t.driverId != r.driverId  
}

// If a car is driven by a driver, it can't be available
fact carInTravelNotAvailable{
no t:Travel | t.car.isAvailable = False
}


// If a car has been requested, it can't be available
fact carRequestedNotAvailable{
no r:Request | r.car.isAvailable = False
}

//If a car is driven, it has been requested before
fact carDrivenisRequested{
all t:Travel | one r: Request| t.reqNumber = r.reqNumber
}

fact finalFeeResult{
all f:FinishedTravel | f.finalFee = f.normalFee  - (f.normalFee- f.normalFee.mul[f.discounts.passengersDiscount])
                                                                      - (f.normalFee- f.normalFee.mul[f.discounts.batteryDiscount])	
																	  - (f.normalFee- f.normalFee.mul[f.discounts.plugDiscount])	
																	  +(f.normalFee- f.normalFee.mul[f.penalty.distancePenalty])
}


////ASSERTIONS ////

//If the requested car has not been picked up within an hour, the system makes the car available again
assert requestTimeExcedeed{
all r:Request, c:CurrentTime | (((c.hours = r.start.hours) && (c.minutes - r.start.minutes > 60) || ((c.hours < r.start.hours) && (c.minutes < r.start.minutes))) implies r.car.isAvailable = True)
}

// A driver can't do 2 requests in 1 hour
assert noTwoCloseRequests{
no r1, r2: Request | r1.driverId = r2.driverId && ( 
	((r1.start.hours < r2.start.hours) && (r1.start.minutes < r2.start.minutes)) ||
	((r2.start.hours < r1.start.hours) && (r2.start.minutes < r1.start.minutes))
	) 
}

fact passengersDiscount{
all f: FinishedTravel | (f.passengers > 1) implies (f.(discounts.passengersDiscount)) = 10
}

fact batteryDiscount{
all f: FinishedTravel | (f.car.charge.batteryLevel > 50) implies (f.(discounts.batteryDiscount)) = 20
}

fact pluggedDiscount{
all f: FinishedTravel | (f.car.charge.batteryLevel > 50) implies (f.(discounts.batteryDiscount)) = 20
}

pred show{}

run show for 3

check requestTimeExcedeed for 3
check noTwoCloseRequests for 3
