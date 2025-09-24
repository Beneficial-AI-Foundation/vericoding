// <vc-preamble>
class Counter {

  var value : int ;

  constructor init() 
  ensures value == 0;
  {
    value := 0 ;
  }
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method getValue() returns (x:int)
  ensures x == value;
// </vc-spec>
// <vc-code>
{
    x := value ;
}
// </vc-code>

}