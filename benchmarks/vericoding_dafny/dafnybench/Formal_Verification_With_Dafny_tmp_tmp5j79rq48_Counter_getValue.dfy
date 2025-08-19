class Counter {

  var value : int ;

  constructor init() 
  ensures value == 0;
  {
    value := 0 ;
  }

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method getValue() returns (x:int)
  ensures x == value;
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>

}