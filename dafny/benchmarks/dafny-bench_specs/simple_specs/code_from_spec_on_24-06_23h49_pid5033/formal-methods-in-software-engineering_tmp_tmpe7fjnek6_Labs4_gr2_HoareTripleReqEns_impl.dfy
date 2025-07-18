//IMPL HoareTripleReqEns
method HoareTripleReqEns(i: int, k: int) returns (k': int)
	// (| k == i*i |) k := k + 2 * i +1; (| k = (i+1)*(i+1) |)
	requires k == i*i
	ensures k' == (i+1)*(i+1)
{
	k' := k + 2 * i + 1;
}