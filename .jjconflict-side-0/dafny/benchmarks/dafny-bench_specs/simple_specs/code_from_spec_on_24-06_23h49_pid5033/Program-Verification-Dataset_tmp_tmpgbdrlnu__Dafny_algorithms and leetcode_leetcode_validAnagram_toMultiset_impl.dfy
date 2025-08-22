//IMPL toMultiset
method toMultiset(s: string) returns (mset: multiset<char>)
  ensures multiset(s) == mset
{
  /* code modified by LLM (iteration 1): Direct assignment using built-in multiset conversion */
  mset := multiset(s);
}