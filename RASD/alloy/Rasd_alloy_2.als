// ---- SIGNATURES ----
open util/integer

sig Strings{}



enum CarStatus{AVAILABLE, RESERVED, CHARGING}


sig User{
	name:Strings,
	surname: Strings,
	username: Strings,
}

sig GPSPosition{
	latitude: Int,
	longitude: Int
}

sig Car{
	plaqueNumber: one Int,
	seats: one Int,
	position: GPSPosition,
	status: CarStatus
}{
	seats>0
}

sig Request{
	id: Strings,
	user: User,	
	car: Car
}


sig SafeArea{
	availableCars: Int,
	chargingStations: Int,
	positions: set GPSPosition
}{availableCars >= 0
	chargingStations >=0}

sig Travel{
	driver: User,
	id: Strings,
    car:Car,
	passengers: Int,
	pickPosition: GPSPosition,
	leftPosition: GPSPosition
}{passengers >=0}

//FACTS
fact NoDuplicatedUsernames{
 no u1,u2:User | (u1!=u2) && (u1.username = u2.username)
}

fact NoTravelWithToManyPassengers{
	no t:Travel | (t.passengers > t.car.seats)
}

fact  NoCarsWithSamePlaqueNumber{

no c1,c2: Car | (c1!=c2) && (c1.plaqueNumber = c2.plaqueNumber)

}

fact RequestedCarsReserved{

all r:Request | (r.car.status = RESERVED)

}

fact DrivenCarsReserved{
all t:Travel | (t.car.status = RESERVED)
}

fact RequestedCarsInSafeAreas{
all r:Request | one s:SafeArea| r.car.position in s.positions
}

fact PickedCarInSafeArea{
all t:Travel | one s:SafeArea| t.pickPosition in s.positions
}

fact LeftCarsInSafeArea{
all t:Travel | one s:SafeArea| t.leftPosition in s.positions
}

fact TravelCorrespondsToRequest{
all t:Travel | one r:Request | r.id = t.id
}

fact UserIsTheOnlyDriver{
no t:Travel, r:Request | (t.id = r.id) && (t.driver != r.user)
}

fact DifferentRequestsDifferentCars{
no r1,r2:Request | (r1!=r2) && (r1.car = r2.car)
}


fact DifferentRequestsDifferentUsers{
no r1,r2:Request | (r1!=r2) && (r1.user = r2.user)
}


fact DifferentTravelsDifferentUsers{
no t1,t2:Request | (t1!=t2) && (t1.user = t2.user)
}

// ASSERTIONS 

assert ReservedCarsNotAvailable{
all r:Request | (r.car.status != AVAILABLE)
}
check ReservedCars

assert DrivenCarsNotAvailableAndNotCharging{
all t:Travel| (t.car.status != AVAILABLE) && (t.car.status != CHARGING)
} check DrivenCars



//SHOW

pred show{
	#User = 2
}

run show 
