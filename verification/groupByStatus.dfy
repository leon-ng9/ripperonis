datatype State = ORDERING | WAITING | STORED | BAD

method FlagSort(flag: array<State>)

requires flag!=null
ensures forall i,j:: 0 <= i < j< flag.Length && flag[i]==WAITING   ==> ( flag[j] != ORDERING   )
ensures forall i,j:: 0 <= i < j< flag.Length && flag[i]==STORED ==> ( flag[j] != ORDERING && flag[j] != WAITING )
ensures forall i,j:: 0 <= i < j< flag.Length && flag[i]==BAD  ==> ( flag[j] == BAD )

modifies flag;
{
    var waiting := 0;
    var next := 0;
    var bad := flag.Length;
    while (next != bad)
    invariant 0 <= waiting <= next <= bad <= flag.Length
    invariant forall i:: 0     <= i < waiting        ==> flag[i]==ORDERING
	invariant forall i:: waiting  <= i < next        ==> flag[i]==WAITING || flag[i] == STORED
    invariant forall i:: bad <= i < flag.Length ==> flag[i]==BAD
    {
            match (flag[next])
            {
            case WAITING   => next:=next+1;
            
            case STORED => next:=next+1;
            
            case BAD  => bad:=bad-1;
                           flag[next], flag[bad] := flag[bad], flag[next];
                           
            case ORDERING    => flag[next], flag[waiting] := flag[waiting], flag[next];
                           next:=next+1;
                           waiting:=waiting+1;
            }
    }
    
    next := waiting;
    var stored := waiting;
    
    while (next != bad)
    invariant 0 <= waiting <= stored <= next <= bad <= flag.Length
    invariant forall i:: 0      <= i < waiting        ==> (flag[i]==ORDERING )
    invariant forall i:: waiting   <= i < stored      ==> (flag[i]==WAITING )
    invariant forall i:: stored <= i < next        ==> (flag[i]==STORED )
    invariant forall i:: next   <= i < bad       ==> (flag[i]==STORED || flag[i]==WAITING)
    invariant forall i:: bad  <= i < flag.Length ==> (flag[i]==BAD)
    {
        match (flag[next])
        {
            case STORED => next := next + 1;
            case WAITING   => flag[next], flag[stored] := flag[stored], flag[next];
                           next:=next+1;
                           stored:=stored+1;
        }
    }
}

method Main()
{
  var flag: array<State> := new State[16];
  flag[0], flag[1], flag[2], flag[3], flag[4], flag[5],flag[6], flag[7], flag[8], flag[9], flag[10], flag[11],flag[12], flag[13], flag[14], flag[15]
   := WAITING, ORDERING, STORED, WAITING, BAD, WAITING, WAITING, ORDERING, STORED, WAITING, BAD, WAITING, WAITING, ORDERING, STORED, WAITING;
  FlagSort(flag);
  print flag[..], '\n';
}




