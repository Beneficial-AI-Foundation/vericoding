// The specification requires:
// - `modifies this`value`: the method can modify the value field
// - `requires value >= 0`: the value must be non-negative before the call
// - `ensures value == old(value) + 1`: after the call, value should be one more than it was before

// The implementation is straightforward - I just need to increment the value by 1.

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

method inc()
  modifies this`value
  requires value >= 0;
  ensures value == old(value) + 1;
// </vc-spec>
// <vc-code>
{
  value := value + 1;
}
// </vc-code>

}