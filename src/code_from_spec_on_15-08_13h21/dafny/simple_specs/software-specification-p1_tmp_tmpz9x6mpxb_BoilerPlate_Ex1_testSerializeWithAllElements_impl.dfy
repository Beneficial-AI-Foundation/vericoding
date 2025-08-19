//ATOM
datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)

//ATOM
datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)

//ATOM
function serialise<V>(t : Tree<V>) : seq<Code<V>> 
{
 match t {
  case Leaf(v) => [ CLf(v) ]
  case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
  case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
 }
}

//IMPL 
method testSerializeWithAllElements()
{
    var leaf1 := Leaf(1);
    var leaf2 := Leaf(2);
    var leaf3 := Leaf(3);
    
    var singleNode := SingleNode(4, leaf1);
    var doubleNode := DoubleNode(5, leaf2, leaf3);
    
    var complexTree := DoubleNode(6, singleNode, doubleNode);
    
    var result := serialise(complexTree);
    
    /* code modified by LLM (iteration 1): corrected expected result based on actual serialization order */
    assert result == [CLf(3), CLf(2), CDNd(5), CLf(1), CSNd(4), CDNd(6)];
}