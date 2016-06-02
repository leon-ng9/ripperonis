module PriorityQueue{
	class {:autocontracts} PriorityQueue
	{
	
		ghost var shadow: set<int>;
		var a: array<int>;
		var n:int;

		predicate Valid()
	   {
		  a!=null && a.Length!=0 && 0<=n<=a.Length && 
		  forall i:: 0 <= i < n ==> a[i] in shadow
		  && forall k:nat, i:nat ::  i == (k-1)/2 && 0 <= k < n ==> (a[k] >= a[i])
	   }

		constructor Init()
		ensures shadow == {};
		{
			shadow :={};
			a, n := new int[10], 0;
		}

		method enqueue(d: int)
		modifies a
		//requires forall k :: 1 <= k < n ==> (shadow[k] >= shadow[(k-1)/2])
		ensures forall i :: i in shadow <==> i in old(shadow) || i == d
		{
			//insert
			if n == a.Length
			{
				var b := a;
				b := new int[2*a.Length];
				forall (i | 0<=i<n )
					{ b[i] := a[i]; }
				a := b;
			}
			a[n]:= d;
			shadow := shadow + {d};

			//adjust the position

			var index := n;
			var next := (index - 1) / 2;

			while(index > 0)
			modifies a
			invariant 0 <= index <= n< a.Length
			invariant forall i:: 0 <= i <= n ==> a[i] in shadow
			invariant next == (index - 1) / 2
			invariant forall k:nat, i:nat ::  i == (k-1)/2 && 0 <= k <= n && k != index ==> a[i] <= a[k]
			invariant forall k:nat, i:nat :: (k - 1)/2 == index && i == ((k - 1)/2 - 1)/2 && i >= 0 && k <= n ==> a[i] <= a[k]
			{
			
				if(a[next] > a[index])
				{
					a[next], a[index]:= a[index], a[next];
				}
				index := next;
				next := (index - 1) / 2;
			}

			n := n+1;
		}


		method dequeue() returns(result:int )
		requires shadow != {}
		requires a != null && n <= a.Length
		requires n >= 1
		ensures forall i :: 0 <= i < n ==> a[i] in old(a[1..])
		ensures result == old(a[0])
		ensures n == old(n) - 1
		{
			result := a[0];
			a[0] := a[n-1];
			n := n - 1;
		
			var index := 0;
		
			while(index * 2 + 1 < n)
			modifies a
			invariant 0 <= index <= n< a.Length
			invariant forall i :: 0 <= i < n ==> a[i] in old(a[1..])
			invariant forall i:: 0 <= i < n ==> a[i] in shadow
			invariant forall k:nat, i:nat ::  i == (k-1)/2 && 0 <= k < n && i != index ==> a[i] <= a[k]
			invariant forall k:nat, i:nat :: (k - 1)/2 == index && i == ((k - 1)/2 - 1)/2 && i >= 0 && k < n ==> a[i] <= a[k]
			{
				var i:int;
				if(index * 2 + 2 < n && a[index * 2 + 2] < a[index * 2 + 1]){
					i := index * 2 + 2;
				}else{
					i := index * 2 + 1;
				}
				if(a[index] >= a[i]){
					a[i],a[index] := a[index],a[i];
				}
				index := i;
			}
		}

		function method isEmpty(n:int):bool
		{
			if n == 0 then true
			else false
		}
	}

}

