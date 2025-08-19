//IMPL 
method toMultiset(s: string) returns (mset: multiset<char>)
  ensures multiset(s) == mset
{
  mset := multiset(s);
}