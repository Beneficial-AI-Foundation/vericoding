// SPEC 
method M()
{
}



// SPEC 


method N()
  ensures (forall b: bool :: b || !b) || 2 != 2;
