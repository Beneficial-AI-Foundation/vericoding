//ATOM
method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
{
  c := {};
  assume forall x :: x in a && x in b <==> x in c;
  return c;
}

//IMPL 
method TesterFilter()
{
  var testSeq := ['a', 'b', 'c', 'a'];
  var testSet := {'a', 'c', 'd'};
  var result := Filter(testSeq, testSet);
  
  // The result should contain 'a' and 'c' since they appear in both testSeq and testSet
  // 'd' is not in the result since it's not in testSeq
  // 'b' is not in the result since it's not in testSet
}