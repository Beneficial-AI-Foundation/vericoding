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



  // The method maintains the invariant that the number of available spaces availableSpaces is updated correctly
  // based on the current state of the car park and whether it is a weekend or not
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method checkAvailability() returns (availableSpaces: int) 
    requires true
    modifies this
    ensures weekend ==> availableSpaces == (normalSpaces - old(|carPark|)) + (reservedSpaces - old(|reservedCarPark|)) - badParkingBuffer;
    ensures !weekend ==> availableSpaces == (normalSpaces - old(|carPark|)) - badParkingBuffer;
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend) && subscriptions == old(subscriptions);
// </vc-spec>
// <vc-code>
{
    if (weekend){
      availableSpaces := (normalSpaces - |carPark|) + (reservedSpaces - |reservedCarPark|) - badParkingBuffer;
    } else{
      availableSpaces := (normalSpaces - |carPark|) - badParkingBuffer;
    }
}
// </vc-code>

}



// Added due to timeout in Main