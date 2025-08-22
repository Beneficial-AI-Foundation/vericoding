//IMPL 
method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
{
  xs := [];
  var remaining := s;
  
  while remaining != {}
    invariant multiset(s) == multiset(xs) + multiset(remaining)
    decreases |remaining|
  {
    var x :| x in remaining;
    xs := xs + [x];
    remaining := remaining - {x};
  }
}