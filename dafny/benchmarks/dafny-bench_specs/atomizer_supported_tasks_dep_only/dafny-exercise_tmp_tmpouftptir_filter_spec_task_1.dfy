// SPEC 
method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
{
}


//ATOM_PLACEHOLDER_TesterFilter



