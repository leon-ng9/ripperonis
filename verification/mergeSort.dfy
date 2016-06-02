method mergeSort(a:array<int>, holder:array<int>, start:int, end:int )
requires a != null && holder != null
requires a.Length == holder.Length
requires 0 <= start < end <= a.Length
ensures sorted(a, start, end)
decreases end - start
modifies a, holder
{
	if(end - start == 1){
		a[start] := holder[start];
	}else{
		var mid:int := (end + start) / 2;
		mergeSort(holder,a, mid, end);
		mergeSort(holder,a, start, mid);
		assume sorted(holder,mid,end);
		merge(a,holder,start, mid, end);
		
	}
}

method merge(a:array<int>, holder:array<int>, start:int, mid:int, end:int )
requires a != null && holder != null
requires a.Length == holder.Length
requires 0 <= start <= mid < end <= a.Length
requires sorted(holder,start,mid)
requires sorted(holder,mid, end)
ensures sorted(a,start,end)
modifies a
{
		var i:nat := start;
		var j: nat := mid;
		var curr:nat := start;

		while (i < mid && j < end)
		decreases mid - i + end - j
		invariant i <= curr <= j
		invariant start <= i <= mid <= j <= end
		invariant sorted(holder,i,mid) 
		invariant i < mid ==> (curr > start ==> holder[i] >= a[curr-1])
		invariant j < end ==> sorted(holder,j,end) && (curr > start ==> holder[j] >= a[curr-1])
		invariant j - mid + i == curr
		invariant sorted(a,start, curr)
		{
			if(holder[i] <= holder[j]){
				a[curr] := holder[i];
				i := i + 1;
			}else{
				a[curr] := holder[j];
				j := j + 1;
			}
			curr := curr + 1;
		}

		while(i < mid)
		invariant start <= i <= mid
		invariant i <= curr <= end
		invariant i <= mid
		invariant sorted(holder,i,mid)
		invariant sorted(holder, j, end)
		invariant mid - i + curr == j
		invariant sorted(a,start,curr)
		invariant curr > start && j < end ==> a[curr - 1] <= holder[j]
		invariant curr > start && i < mid ==> a[curr - 1] <= holder[i]
		{
			a[curr] := holder[i];
			i := i + 1;
			curr := curr + 1;
		}

		while( j < end)
		invariant curr == j
		invariant j <= end
		invariant sorted(holder,j, end)
		invariant curr > start && j < end ==> holder[j] >= a[curr - 1]
		invariant sorted(a,start,curr)
		{
			a[curr] := holder[j];
			j := j + 1;
			curr := curr + 1;
		}
}

predicate sorted(a:array<int>, start:int, end:int)
reads a
requires a!= null
requires 0 <= start <= end <= a.Length
{
	forall j,k :: start <= j < k < end ==> a[j]<= a[k]
}
