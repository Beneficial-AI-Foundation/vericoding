class CountdownClass {
  var impl_countdown: int

  method DecrementCountdown() 
    modifies this
  {
    impl_countdown := impl_countdown - 1;
  }
}