//ATOM

method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
{
  c := {};
  assume forall x :: x in a && x in b <==> x in c;
  return c;
}


// SPEC

method TesterFilter()
{
}