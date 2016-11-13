// ---- SIGNATURES ----
open util/integer

sig Strings{}

enum CarStatus{AVAILABLE, RESERVED, CHARGING}

sig User{
	username: Strings,
}

sig GPSPosition{}

sig Car{
	plaqueNumber: one Int,
	seats: one Int,
	position: GPSPosition,
	status: CarStatus
}{	seats>0
}

sig Request{
//	id: Strings,
	user: User,	
	car: Car
}

sig SafeArea{
	cars: set Car,
	chargingStations: Int,
	positions: some GPSPosition
}{ chargingStations >=0}

sig Travel{
	request: Request,
	passengers: Int,
	pickPosition: GPSPosition,
	leftPosition: GPSPosition
}
{passengers >=0}

//FACTS
fact NoDuplicatedUsernames{
	no u1,u2:User | (u1!=u2) && (u1.username = u2.username)
}

fact NoTravelWithToManyPassengers{
	no t:Travel | (t.passengers > t.request.car.seats)
}

fact  NoCarsWithSamePlaqueNumber{
	no c1,c2: Car | (c1!=c2) && (c1.plaqueNumber = c2.plaqueNumber)
}

fact RequestedCarsReserved{
	no c:Car | c.status=RESERVED && no r:Request | r.car=c
}

fact DrivenCarsReserved{
	all t:Travel | (t.request.car.status = RESERVED)
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
	all r:Request | one t:Travel | t.request=r
}

fact UserIsTheOnlyDriver{
	no t:Travel, r:Request | (t.request = r) && (t.request.user != r.user)
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

fact DifferentGPSPositionInDifferentSafeAreas{
	no s1,s2:SafeArea, gps:GPSPosition | s1 != s2 and gps in s1.positions and gps in s2.positions
}

fact CarInDifferentSafeArea{
all s1,s2:SafeArea | no c:Car | s1!=s2 and c in s1.cars and c in s2.cars
}

fact ChargingOnlyInSafeArea{
all c:Car | c.status=CHARGING => (one s:SafeArea | c in s.cars and c.position in s.positions)
}

// ASSERTIONS 

assert ReservedCarsNotAvailable2{
all r:Request | (r.car.status != AVAILABLE)
}
check ReservedCarsNotAvailable2

assert DrivenCarsNotAvailableAndNotCharging{
all t:Travel| (t.request.car.status != AVAILABLE) && (t.request.car.status != CHARGING)
}
check DrivenCarsNotAvailableAndNotCharging

assert ReservedCarMustHaveAReservation {
all c:Car | c.status=RESERVED => one r:Request | r.car = c
}
check ReservedCarMustHaveAReservation

//SHOW

pred show{
#Request  = 2
#User = 4
}

run show for 5
