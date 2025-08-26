class Counter {

  var value : int ;

// <vc-spec>
  constructor init() 
  ensures value == 0;
  {
    value := 0 ;
  }

// <vc-helpers>
// </vc-helpers>

method getValue() returns (x:int)
  ensures x == value;
// </vc-spec>
// <vc-code>
{
  x := value;
}
// </vc-code>

}