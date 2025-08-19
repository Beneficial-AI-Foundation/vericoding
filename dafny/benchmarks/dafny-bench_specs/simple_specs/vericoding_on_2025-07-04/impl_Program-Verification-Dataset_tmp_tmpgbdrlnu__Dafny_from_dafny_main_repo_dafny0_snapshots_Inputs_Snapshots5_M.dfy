//ATOM
method N()
  ensures (forall b: bool :: b || !b) || 2 != 2
{
}

//IMPL N
/* code modified by LLM (iteration 1): Added proper spec name and moved ensures clause to correct position */
method M()
  ensures (forall b: bool :: b || !b) || 2 != 2
{
}