public class Quicksort {

    // Write formal pre- and post-conditions for this method.
    /*@ requires a != null && a.length > 0;
      @ requires \typeof(ulimit) <: \type(int) && \typeof(llimit) <: \type(int);
      @ requires 0 <= llimit && llimit < ulimit;
      @ requires llimit < ulimit && ulimit < a.length;
      @ ensures a != null;
      @ ensures (\forall int i; (0 < i && i < a.length) ==> a[i-1] <= a[i]);
     */
    public static void sort(int[] a, int ulimit, int llimit)
    {
        quicksort(a, 0, a.length, ulimit, llimit);
    }

    // Write pre-conditions for this method.
    //@ modifies a[*];
    //@ requires a != null && a.length > 0;
    //@ requires 0 <= start && start <= a.length;
    //@ requires 0 <= stop && stop <= a.length;
    // Write post-conditions for this method.
    //@ ensures a != null;
    private static void quicksort(int[] a, int start, int stop, int ulimit, int llimit)
    {
        // assert 0 <= start && start <= a.length;
	// assert 0 <= stop && stop <= a.length;
        if (stop - start > 1) {
            int p = pivot(a, start, stop, ulimit, llimit);
	    // assert start <= p;
	    // assert 0 <= p && p < a.length;
	    // assert p + 1 <= stop;
            quicksort(a, start, p, a[p], llimit);
            quicksort(a, p+1, stop, ulimit, a[p]);
        }
    }

    // Write pre-conditions for this method.
    //@ modifies a[*];
    //@ requires a != null && a.length > 0;
    //@ requires 0 <= start && start < a.length;
    //@ requires start + 1 <= stop && stop <= a.length;
    // Write post-conditions for this method. 
    //@ ensures 0 <= \result && \result < a.length;
    //@ ensures a != null;
    private static int pivot(int[] a, int start, int stop, int ulimit, int llimit)
    {
        int p = partition(a, a[start], start+1, stop, ulimit, llimit);
        // assert \typeof(a[start]) <: \type(int);
	// assert 0 <= start && start < stop - 1;
        // assert 0 <= p && p < a.length;
        if (start < p)
            swap(a, start, p);
        return p;
    }

    // Write pre-conditions for this method.
    //@ modifies a[*];
    //@ requires a != null && a.length > 0;
    //@ requires \typeof(pivot) <: \type(int);
    //@ requires 0 < start && start <= a.length;
    //@ requires 0 < stop && stop <= a.length;
    // Write post-conditions for this method.
    //@ ensures 0 <= \result && \result < a.length;
    private static int partition(int[] a, int pivot, int start, int stop, int ulimit, int llimit)
    {
        if (start >= stop) {
            // assert 0 < start;
            // assert 0 < stop; 
            return start - 1;
        } if (a[start] < pivot)
            return partition(a, pivot, start + 1, stop, ulimit, llimit);
        if (a[--stop] > pivot)
            return partition(a, pivot, start, stop, ulimit, llimit);
        if (start < stop) {
 	    // assert 0 < start && start <= a.length;
            // assert 0 < stop && stop <= a.length;
            swap(a, start, stop);
            return partition(a, pivot, start+1, stop, ulimit, llimit);
        } else {
            // assert 0 < start;
            return start;
        }
    }

    /*@ requires a != null;
      @ requires 0 <= i && i < a.length;
      @ requires 0 <= j && j < a.length;
      @ modifies a[i], a[j];
      @ ensures a[i] == \old(a[j]) && a[j] == \old(a[i]);
      */    
    public static void swap(int[] a, int i, int j)
    {
        int temp = a[i];
        a[i] = a[j];
        a[j] = temp;
    }
}
