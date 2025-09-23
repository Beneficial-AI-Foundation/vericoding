// <vc-preamble>
class {:autocontracts} CarPark {
    const totalSpaces: nat := 10;
    const normalSpaces: nat:= 7;
    const reservedSpaces: nat := 3;
    const badParkingBuffer: int := 5;

    var weekend: bool;
    var subscriptions: set<string>;
    var carPark: set<string>;
    var reservedCarPark: set<string>;

    constructor()
    requires true
    ensures this.subscriptions == {} && this.carPark == {} && this.reservedCarPark == {} && this.weekend == false;
    {

    this.subscriptions := {};
    this.carPark := {};
    this.reservedCarPark := {};
    this.weekend := false;
    }

    // This predicate checks if the car park is in a valid state at all times.
    // It checks if the sets of cars in the car park and the reserved car park are disjoint and share no values,
    // the total number of cars in the car park is less than or equal to the total number of spaces in
    // the car park plus the bad parking buffer, the number of normal spaces plus reserved spaces is
    // equal to the total number of spaces, and the number of cars in the reserved car park is less than or equal
    // to the number of reserved spaces
    ghost predicate Valid()
    reads this
    {
                          carPark * reservedCarPark == {} && |carPark| <= totalSpaces + badParkingBuffer && (normalSpaces + reservedSpaces) == totalSpaces && |reservedCarPark| <= reservedSpaces
    }



  // The method maintains the invariant that if success is true, then the car parameter is added to the
  // reservedCarPark set and the number of cars in the reservedCarPark set is less than the number of
  // reserved spaces and either the weekend variable is true or the car parameter is in the subscriptions set.
  // Otherwise, the carPark and reservedCarPark sets are not modified
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method enterReservedCarPark(car: string) returns (success: bool) 
    requires true
    modifies this;

    ensures success ==> (car !in old(carPark)) && (car !in old(reservedCarPark)) && (old(|reservedCarPark|) < reservedSpaces) && (car in subscriptions || weekend == true);
    ensures success ==> reservedCarPark == old(reservedCarPark) + {car};
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark);
    ensures !success ==> (car in old(carPark)) || (car in old(reservedCarPark) || (old(|reservedCarPark|) >= reservedSpaces) || (car !in subscriptions && weekend == false));
    ensures subscriptions == old(subscriptions) && carPark == old(carPark) && weekend == old(weekend);
    ensures weekend == old(weekend) && subscriptions == old(subscriptions);
// </vc-spec>
// <vc-code>
{
    if (|reservedCarPark| >= reservedSpaces || car in carPark || car in reservedCarPark || (car !in subscriptions && weekend == false)) {
      return false;
    }
    else
    {
      reservedCarPark := reservedCarPark + {car};
      return true;
    }
}
// </vc-code>

}



// Added due to timeout in Main