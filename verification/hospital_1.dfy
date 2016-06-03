
datatype BloodType = Ap|An|Bp|Bn|Op|On|ABp|ABn
datatype State = ORDERING | WAITING | STORED | USED | GONE
class {:autocontracts} Donor
{
    var bt: BloodType;
    predicate Valid()
    {
      true
    }
}
class {:autocontracts} Blood
{
    var date: int;
    var expireDate: int;
    var hospital: Hospital;
    var donor: Donor;
    var used: bool;
    var amount: int ;
    predicate Valid()
    {
        donor != null &&
        hospital != null
    }
    method updateDate(){}
    function method isExpired():bool
    reads this
    {
        expireDate > 20
    }
}

class {:autocontracts}Record
{
    var blood:Blood;
    var donor: Donor;
    var state: State;
    predicate Valid()
    {
      blood != null && donor != null && blood.Valid() && donor.Valid()
    }
    function method hasBlood():bool
    reads this
    {
      blood != null
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
    method add(r: Record)
    requires r != null
    requires r.blood != null
    modifies r;
    requires r.state == ORDERING
    ensures r.state == WAITING
    ensures records == old(records) + [r]
    {
        r.state := WAITING;
        records := records + [r];
    }
    
    method update(r: Record)
    requires r != null
    modifies r
    modifies r.blood
    requires r.state == WAITING
    requires r.blood != null
    ensures r.state == STORED
    ensures r.blood != null;
    ensures r.blood.hospital == this
    {
        r.state := STORED;
        r.blood.hospital := this;
        
    }
        
    method remove(r: Record)
    requires r != null
    modifies r
    ensures r.state == GONE
    {
        r.state := GONE;
    }
    
    
    method getAvailableBlood() returns(bloods: seq<Blood>)
    requires forall i:: i in records ==> i.Valid() && i.blood.Valid()
    ensures forall i:: (i in records && i.state == STORED && !( i.blood.isExpired() || i.blood.used ) ) ==> i.blood in bloods
    ensures forall i :: i in bloods ==> i != null && i.Valid() && !(i.isExpired() || i.used)
    {
        bloods := [];
        var i:= 0;
        while( i < |records|)
        invariant 0 <= i <= |records|
        invariant forall i:: i in records ==> i.Valid() && i.blood.Valid()
        invariant forall j :: 0 <= j < |records| ==> (records[j] != null && records[j].blood != null )
        invariant forall j:: (0 <= j < i && records[j].state == STORED && !( records[j].blood.isExpired() || records[j].blood.used ) ) ==> records[j].blood in bloods
        invariant forall j:: (j in bloods ) ==> j != null && j.Valid()&& !(j.isExpired() || j.used)
        {   
            if(records[i].state == STORED)
            {
                var b := records[i].blood;
                if(!(b.isExpired() || b.used))
                {
                    bloods := bloods + [b];
                }
            }
            i := i + 1;
        }
    }
    
    method getPendingRecords() returns (result: seq<Record>)
    ensures forall j:: (j in records && j.state == WAITING ) ==> j in result
    {
        result := [];
        var i := 0;
        while( i < |records|)
        invariant 0 <= i <= |records|
        invariant forall j :: 0 <= j < |records| ==> (records[j] != null && records[j].blood != null )
        invariant forall j:: (0 <= j < i && records[j].state == WAITING) ==> records[j] in result
        {   
            if(records[i].state == WAITING)
            {
                result := result + [records[i]];
            }
            i := i + 1;
        }
    }
    
    method summary() returns(m: map<BloodType, int>)
    requires forall i:: i in records ==> i.Valid() && i.blood.Valid()
    {
		var allBlood := getAvailableBlood();
		m := map[];
		var it := 0;
		while( it< |allBlood|)
        invariant 0 <= it <= |allBlood|
        invariant forall i:: i in records ==> i.Valid() && i.blood.Valid()
		invariant forall i:: (i in records && i.state == STORED && !( i.blood.isExpired() || i.blood.used ) ) ==> i.blood in allBlood
        invariant forall i :: (i in allBlood) ==> i != null && i.Valid() && !(i.isExpired() || i.used)
    {
		    var b := allBlood[it];
            //Dafny is apparently not clever enough to transform between 
            // in and index
            assume b != null && b.Valid();
		    if( b.donor.bt in m)
		    {
		        m := m[b.donor.bt := m[b.donor.bt] + b.amount];
		    }
		    else
		    {
		        m := m[b.donor.bt := b.amount];
		    }
        it := it + 1;
		}
	}
}
