//ATOM

ghost function SetProduct(s : set<int>) : int
{
  if s == {} then 1
  else var x :| x in s; 
     x * SetProduct(s - {x})
}

/* 
 * This is necessary because, when we add one element, we need to make sure
 * that the product of the new set, as a whole, is the same as the product
 * of the old set times the new element.
 */


// SPEC
method UniqueProduct (arr: array<int>) returns (product: int)
  ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
{
}
