
datatype BloodType = Ap|An|Bp|Bn|Op|On|ABp|ABn
datatype State = ORDERING | WAITING | STORED | USED | GONE
class {:autocontracts} Blood
{
    var date: int;
    var expireDate: int;
    var used: bool;
    var amount: int ;
    var bt: BloodType;
    
    predicate Valid()
    {
        donor != null &&
        hospital != null
    }
    method updateDate(){}
    
}

class {:autocontracts}Record
{
    var blood:Blood;
    var state: State;
    var amount: int ;
    var bt: BloodType;
    var expireDate: int;
    
    predicate Valid()
    {
      blood != null && donor != null && blood.Valid() && donor.Valid()
    }
    function method hasBlood():bool
    reads this
    {
      blood != null
    }
    function method expired():bool
    reads this
    {
        expireDate > 20
    }
}
class {:autocontracts} Hospital 
{
    var records: seq<Record>;
    method Init()
    ensures records == [];
    {
        records := [];
    }
    
    predicate Valid()
    reads records
    {
        forall i :: 0 <= i < |records| ==> records[i]!= null && records[i].hasBlood()
    }


    function method sum(s: seq<Record>):int
    {
        if |s| == 0 then 0
        else s[0] + sum(s[1..])
    }
    method requestBlood(amount: int, btype:BloodType) returns(result: seq<Record>)
    requires amount > 0
    ensures result != null
    ensures result != [] ==> sum(result) >= amount
    ensures result != [] ==> (forall r:: r in result ==> (r.state == USED && !r.expired() ))
    {
        result := [];
        var i := 0;
        var total := 0;
        while(i < |records|)
        
        {
            if(total < amount)
            {
                if(records[curr].state == 2 && !records[curr].expired()){
                    if(curr.bt.equals(btype))
                    {
                        result := result + [curr];
                        total := total + curr.amount;
                    }
                }
            }
            i := i + 1;
        }
        
        if(amount > total)
        {
            result := [];
        }
        else
        {
            i := 0;
            while(i < |result|)
            {
                result[i].state := USED;
            }
        }
    }
}

