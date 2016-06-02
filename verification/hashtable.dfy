class {:autocontracts} HashTable {
    
      var hashtable:array<int>;
      var capacity:int;
      var size:int;	
	  ghost var shadow:set<int>;
	
      predicate Valid()
	  reads this, hashtable;
      {
		hashtable!= null && capacity > 0
		&& capacity == hashtable.Length
		&& |shadow| == size
		&& 0 <= size <= capacity
		&& forall i :: i != 0 ==> ((exists j :: 0 <= j < size && hashtable[j] == i ) <==> (i in shadow))
		&& forall i :: hashtable[hash_function(i)] == 0 ==> !(i in shadow)
      }

      method Init(c:int)
	  requires c > 0;
	  ensures c == capacity && size == 0
	  ensures hashtable != null
      {
        hashtable := new int[c]; 
        capacity := c;
        size := 0;
        shadow := {};
        forall (i | 0 <= i < hashtable.Length) {
           hashtable[i] := 0;
        }
      }
      	
     function method hash_function(key:int):(int)
	 reads this, hashtable;
	 requires hashtable!= null && capacity > 0
     {
       var result:int := 0;
       if (key >= 0)
       then key % capacity
       else (key * -1) % capacity
      }

      method Add(val:int)
	  requires val != 0
	  requires size < capacity
	  ensures Valid()
	  ensures shadow == old(shadow) + {val}
	  //ensures hashtable[hash_function(val)] == val || (exists j :: 0 <= j < capacity ==> hashtable[j] == val)
	  ensures size == old(size) + 1
      {
        var i:int := hash_function(val);
		shadow := shadow + {val};
        if (hashtable[i] == 0) {
			hashtable[i] := val;
			size := size + 1;
	    }
	    else {
            var j:int := 0;
            while (hashtable[i] != 0 && j < capacity)
		    invariant 0 <= j <= capacity;
		    invariant 0 <= i < capacity;
		    decreases capacity - j;
            {
				if (i == capacity-1) 
					{i := 0;}
				else {i := i + 1;}
             
				j := j + 1;
 			}

			hashtable[i] := val;
			size := size + 1;
        }
      }
	
}
