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

method dec()
  modifies this`value
  requires value > 0;
  ensures value == old(value) - 1;
// </vc-spec>
// <vc-code>
{
  value := value - 1;
}
// </vc-code>

}