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
method dec()
  modifies this`value
  requires value > 0;
  ensures value == old(value) - 1;
// </vc-spec>
// <vc-code>
{
    value := value - 1 ;
}
// </vc-code>

}