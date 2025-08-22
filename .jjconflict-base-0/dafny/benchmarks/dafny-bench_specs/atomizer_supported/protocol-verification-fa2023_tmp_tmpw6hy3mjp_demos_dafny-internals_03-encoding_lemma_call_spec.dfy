// ATOM 
function f(x: int): int
 f_positive(x: int)
  requires x >= 0
  ensures f(x) >= 0

// ATOM 

lemma f_2_pos()
  ensures f(2) >= 0
{
  f_positive(2);
}


// ATOM 

lemma f_1_1_pos()
  ensures f(1 + 1) >= 0
{
  f_2_pos();
}




