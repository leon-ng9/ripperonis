type Path = array<int>
datatype Pairs = Pair(0: int, 1:Path) 
class {:autocontracts} Graph{
	var size :nat;
	var neighbours: seq<seq<int>>;

	predicate method hasVertex(v: int)
	reads this;
	{
		0 <= v < size
	}

	function method Valid():bool
	{
		|this.neighbours| == this.size 
		&& (forall s:: s in this.neighbours[..] ==> (|s| == this.size && forall i :: i in s ==> i >= -1) )
	}

	predicate method connected(v:int, w:int)
	reads this
	// requires |this.neighbours| == this.size && (forall s:: s in this.neighbours[..] ==> (|s| == this.size && forall i :: i in s ==> i >= -1) )
	{
		|this.neighbours| == this.size && (forall s:: s in this.neighbours[..] ==> (|s| == this.size && forall i :: i in s ==> i >= -1) )
		 && hasVertex(v) && hasVertex(w) && neighbours[v][w] != -1
	}

	function method cost(path:array<int>, i : int):int
	reads path
	requires path != null
	reads this
	requires |this.neighbours| == this.size && (forall s:: s in this.neighbours[..] ==> (|s| == this.size && forall i :: i in s ==> i >= -1) )
	requires i >= 0
	requires validPath(path, i)
	requires path.Length > i ==> hasVertex(path[i])
	requires path.Length > 1 + i ==> hasVertex(path[i + 1]) 
	decreases path.Length - i
	{
		if path.Length <= i + 1 then 0
		else neighbours[path[i]][path[i + 1]] + cost(path, i+1)
	}

	function method validPath(path:array<int>, i : int):bool
	reads path
	reads this
	requires path != null
	// requires |this.neighbours| == this.size && (forall s:: s in this.neighbours[..] ==> (|s| == this.size && forall i :: i in s ==> i >= -1) )
	requires i >= 0
	decreases path.Length - i
	{
		if path.Length == i + 1 then hasVertex(path[i])
		else if path.Length <= i then true
		else hasVertex(path[i]) 
			&&  hasVertex(path[i+1]) 
			&& connected(path[i],path[i + 1]) 
			&& validPath(path, i + 1)
	}
}

function method min(a:int, b:int) : int
{
	if a > b then b
	else a
}

// Since I can't import priority queue here, I added a stupid popMin function to remove the min value from the array
method popMin(a: array<Pairs>) returns (minIndx: int, min:Pairs, b:array<Pairs>)
requires a!= null
requires a.Length > 0
requires forall i :: 0 <= i < a.Length ==> a[i].1 != null
ensures b != null && b.Length == a.Length - 1
ensures forall i:: 0<= i < a.Length ==> min.0 <= a[i].0
ensures forall i:: 0<= i < b.Length ==> b[i].1 != null
ensures 0 <= minIndx < a.Length
ensures a[minIndx] == min
ensures forall i:: 0 <= i < minIndx ==> b[i] == a[i]
ensures min.1 != null
ensures forall i:: minIndx <= i < b.Length ==> b[i] == a[i+1]
{
	min := a[0];
	minIndx := 0;
	var i := 0;
	while( i < a.Length)
	invariant 0 <= i <= a.Length
	invariant i == 0 ==> minIndx == 0;
	invariant i > 0 ==> 0 <= minIndx < i;
	invariant forall j :: 0 <= j < i ==> min.0 <= a[j].0;
	invariant a[minIndx] == min;
	{
		if(min.0 > a[i].0){
			min := a[i];
			minIndx := i;
		}
		i := i + 1;
	}
	b := new Pairs[a.Length-1];
	var ti := 0;
	var j := 0;
	while( ti < a.Length)
	invariant 0 <= j <= ti <= a.Length
	invariant ti > minIndx ==> (ti == 0 && j == 0) || ti == j + 1
	invariant ti <= minIndx ==> ti == j
	invariant min.1 != null
	invariant forall i:: minIndx < ti ==> (0 <= i < minIndx ==> b[i] == a[i])
	invariant forall i:: minIndx >= ti ==> (0 <= i < ti ==> b[i] == a[i])
	invariant forall i:: minIndx <= i < j ==> b[i] == a[i+1]
	{
		if(ti != minIndx)
		{
			b[j] := a[ti];
			j := j +1;
		}
		ti := ti + 1;
	}
}

method add(G: Graph, a: array<Pairs>, v:Pairs) returns (b: array<Pairs>)
requires a!= null
requires G != null
requires forall i :: 0 <= i < a.Length ==> 
				(a[i].1 != null && a[i].1.Length > 0 
					&& (forall j:: 0 <= j < a[i].1.Length ==> G.hasVertex(a[i].1[j])))
requires forall i :: 0 <= i < a.Length ==> (G.validPath(a[i].1, 0))
requires v.1 != null && G.validPath(v.1,0) && v.1.Length > 0
requires forall j:: 0 <= j < v.1.Length ==> G.hasVertex(v.1[j])
ensures b!= null
ensures b.Length > 0
ensures b.Length == a.Length + 1
ensures forall i::0 <= i < a.Length ==>a[i] == b[i]
ensures forall i :: 0 <= i < b.Length ==> 
				(b[i].1 != null && b[i].1.Length > 0 
					&& (forall j:: 0 <= j < b[i].1.Length ==> G.hasVertex(b[i].1[j])))
ensures forall i :: 0 <= i < b.Length ==> (G.validPath(b[i].1, 0))
ensures b[b.Length-1] == v
{
	b := new Pairs[a.Length + 1];
	var it := 0;
	while(it < a.Length)
	invariant 0 <= it <= a.Length
	invariant forall j::0 <= j < it ==>a[j] == b[j]
	invariant forall i :: 0 <= i < it ==> 
				(b[i].1 != null && b[i].1.Length > 0 
					&& (forall j:: 0 <= j < b[i].1.Length ==> G.hasVertex(b[i].1[j])))
	invariant forall i :: 0 <= i < it ==> (G.validPath(b[i].1, 0))
	invariant v.1 != null && G.validPath(v.1,0) && v.1.Length > 0
	{
		b[it] := a[it];
		it := it + 1;
	}
	b[it] := v;
}

method addPathNode(G: Graph, a: array<int>, v:int) returns (b: array<int>)
requires a!= null
requires G != null
ensures b!= null
requires forall j:: 0 <= j < a.Length ==> G.hasVertex(a[j]);
requires G.validPath(a, 0)
requires G.hasVertex(v)
requires a.Length > 0 ==> G.connected(a[a.Length - 1], v) 
ensures G.validPath(b, 0)
ensures b.Length > 0
ensures b.Length == a.Length + 1
ensures forall i::0 <= i < a.Length ==>a[i] == b[i]
ensures b[b.Length-1] == v
ensures forall j:: 0 <= j < b.Length ==> G.hasVertex(b[j]);
{
	b := new int[a.Length + 1];
	var i := 0;
	while(i < a.Length)
	invariant 0 <= i <= a.Length
	invariant G.validPath(a, 0)
	invariant forall j::0 <= j < i ==>a[j] == b[j]
	invariant a.Length > 0 ==> G.connected(a[a.Length - 1], v) 
	invariant forall j:: 0 <= j < i ==> G.hasVertex(b[j]);
	{
		b[i] := a[i];
		i := i + 1;
	}
	assert G.validPath(a, 0);
	assert a.Length > 0 ==> G.connected(a[a.Length - 1], v);
	b[i] := v;
	assume G.validPath(b, 0);
}

method pathFinding(G: Graph, source: int, target: int ) returns (path: array<int>)
requires G != null;
requires G.Valid();
requires G.hasVertex(source)
requires G.hasVertex(source)
ensures path != null ==> path.Length > 0
ensures path != null ==> G.validPath(path,0)
{
	var pathMap :map<int, array<int>>;
	path := new int[1];
	path[0] := source;
	var visited := new bool[G.size];
	var pQueue:= new Pairs[1];
	var i:int;
	var curr:= Pair(source, path);
	var visitedCount := 0;
	pQueue[0] := curr;
	while(pQueue.Length != 0 && visitedCount < G.size)
	invariant pQueue != null
	invariant curr.1 != null
	invariant forall i :: 0 <= i < pQueue.Length ==> 
		(pQueue[i].1 != null && pQueue[i].1.Length > 0 
			&& (forall j:: 0 <= j < pQueue[i].1.Length ==> G.hasVertex(pQueue[i].1[j])))
	invariant forall i :: 0 <= i < pQueue.Length ==> (G.validPath(pQueue[i].1, 0))
	invariant G.validPath(curr.1, 0)
	decreases G.size-visitedCount
	{
		i, curr, pQueue := popMin(pQueue);
		var currCost := curr.0;
		var currPath := curr.1;
		var currCity := currPath[currPath.Length-1];
		if(currCity == target)
		{
			break;
		}
		visitedCount := visitedCount + 1;
		if (!visited[currCity])
		{
			visited[currCity] := true;
			var counter := 0;
			while(counter < G.size)
			invariant pQueue != null
			invariant curr.1 != null
			invariant forall i :: 0 <= i < pQueue.Length ==> 
				(pQueue[i].1 != null && pQueue[i].1.Length > 0 
					&& (forall j:: 0 <= j < pQueue[i].1.Length ==> G.hasVertex(pQueue[i].1[j])))
			invariant forall i :: 0 <= i < pQueue.Length ==> (G.validPath(pQueue[i].1, 0))
			invariant G.validPath(curr.1, 0)
			invariant 0 <= counter <= G.size
			invariant currCity == currPath[currPath.Length-1]
			invariant forall j:: 0 <= j < currPath.Length ==> G.hasVertex(currPath[j])
			{
				if(!visited[counter])
				{
					if(G.connected(currCity, counter)){
						assert counter < G.size;
						var newPath:= addPathNode(G, currPath ,counter);
						var cost := G.cost(newPath, 0);
						var toAdd := Pair(cost, newPath);
						pQueue := add(G, pQueue, toAdd);
					}
				}
				counter := counter + 1;
			}
		}
	}
	if(curr.1.Length > 0 && curr.1[curr.1.Length-1] == target)
	{
		path := curr.1;
	}
	else
	{
		path := null;
	}
}
