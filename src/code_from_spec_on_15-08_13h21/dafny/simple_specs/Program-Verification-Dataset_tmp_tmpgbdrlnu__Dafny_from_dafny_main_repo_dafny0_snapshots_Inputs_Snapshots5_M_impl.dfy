//ATOM
method N()
 /* code modified by LLM (iteration 3): Added explicit trigger attribute to silence warning */
 ensures (forall b: bool {:trigger b || !b} :: b || !b) || 2 != 2
{
}

//IMPL 
method M()
{
}