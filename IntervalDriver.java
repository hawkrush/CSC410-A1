public class IntervalDriver {

    // Do not change or add annotations in this class!
    //@ public invariant this != null;
    
    /*@ requires i1 != null;
      @ requires i2 != null;
      @ ensures \result != null;
      @*/
    OpenInterval joinIntervals(OpenInterval i1, OpenInterval i2) {
	// Returns empty interval if i1 and i2 are non-overlapping.
	
	if (i1.getLow() < i2.getHigh() || i2.getLow() < i1.getHigh()) {
	    return new OpenInterval(0);
	}

		// Joins i1 and i2.
		int low = i1.getLow() < i2.getLow() ? i1.getLow() : i2.getLow();
		int high = i1.getHigh() > i2.getHigh() ? i1.getHigh() : i2.getHigh();

        return new OpenInterval(low, high);
    }
}

class OpenInterval{

    // Do not change implementations in this class!
    private /*@ spec_public @*/ int low;
    private /*@ spec_public @*/ int high;

    // Do not change this invariant!
    //@ invariant low <= high;
    	
    // Creates an non-empty interval.
    /*@ requires \typeof(low) <: \type(int);
      @ requires \typeof(high) <: \type(int);
      @ ensures this != null;
      @ ensures \typeof(this.low) <: \type(int);
      @ ensures \typeof(this.high) <: \type(int);
      @ ensures this.low <= this.high;
      @ ensures (low <= high ==> (this.low == low && this.high == high))
                || (low > high ==> this.low == this.high);
      @*/
    public OpenInterval(int low, int high){
	//this.low = low;
	//this.high = high;
        if (low <= high) {
	    this.low = low;
	    this.high = high;
	} 
        else {
	    this.low = 0;
            this.high = 0;
	}
    }
    
    // Creates an empty interval.
    /*@ requires x == 0;
      @ ensures this != null;
      @ ensures this.low == x;
      @ ensures this.high == x;
      @*/
    public OpenInterval(int x){
	this.low = x;
	this.high = x;
    }	
    
    // Returns lower bound.
    //@ ensures \typeof(\result) <: \type(int); 
    public int getLow(){
	return this.low;
    }
    
    // Returns upper bound.
    //@ ensures \typeof(\result) <: \type(int); 
    public int getHigh(){
	return this.high;
    }

    /*@ requires x != null;
      @ requires \typeof(x.low) <: \type(int);
      @ requires \typeof(x.high) <: \type(int);
      @ requires this != null;
      @ requires \typeof(this.low) <: \type(int);
      @ requires \typeof(this.high) <: \type(int);
      @ ensures \typeof(\result) <: \type(boolean);
      @*/
    public /*@ pure */ boolean equals(OpenInterval x){
	return (this.low == x.low && this.high == x.high);
    }
}
