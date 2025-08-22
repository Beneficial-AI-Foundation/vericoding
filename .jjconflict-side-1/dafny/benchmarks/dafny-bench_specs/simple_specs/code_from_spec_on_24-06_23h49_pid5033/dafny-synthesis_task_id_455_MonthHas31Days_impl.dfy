//IMPL
method MonthHas31Days(month: int) returns (result: bool)
  requires 1 <= month <= 12
  ensures result <==> month in {1, 3, 5, 7, 8, 10, 12}
{
  result := month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12;
  
  /* code modified by LLM (iteration 1): Added assertion to help Dafny verify equivalence between boolean expression and set membership */
  assert result <==> month in {1, 3, 5, 7, 8, 10, 12};
}