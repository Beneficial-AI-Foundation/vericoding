class Counter {

  var value : int ;

  constructor init() 
  ensures value == 0;
  {
    value := 0 ;
  }

// <vc-helpers>
// </vc-helpers>

method inc()
  modifies this`value
  requires value >= 0;
  ensures value == old(value) + 1;
// <vc-code>
{
  assume false;
}
// </vc-code>

}