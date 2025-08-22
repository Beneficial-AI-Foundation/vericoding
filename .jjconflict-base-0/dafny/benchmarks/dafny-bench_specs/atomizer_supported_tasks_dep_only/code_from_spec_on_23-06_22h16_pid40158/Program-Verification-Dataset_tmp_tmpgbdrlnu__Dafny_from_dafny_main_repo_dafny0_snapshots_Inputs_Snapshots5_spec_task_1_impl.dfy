//IMPL 
method M()
{
}

//IMPL 
method N()
  ensures (forall b: bool :: b || !b) || 2 != 2;
{
}