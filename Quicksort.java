public class Quicksort {

    // Write formal pre- and post-conditions for this method.
    /*@ requires a != null && a.length > 0;
      @ requires \typeof(ulimit) <: \type(int) && \typeof(llimit) <: \type(int);
      @ requires ulimit > 0 && ulimit < a.length;
      @ requires llimit >= 0 && llimit < ulimit;
      @ ensures (\forall int i; 0 < i && i < a.length ==> a[i-1] <= a[i]);
     */
    public static void sort(int[] a, int ulimit, int llimit)
    {
        quicksort(a, 0, a.length, ulimit, llimit);
    }

    // Write pre-conditions for this method.
    //@ modifies a[*];
    //@ requires start >= 0 && start <= stop;
    //@ requires stop >= start && stop <= a.length;
    // Write post-conditions for this method.
    private static void quicksort(int[] a, int start, int stop, int ulimit, int llimit)
    {
        if (stop - start > 1) {
            int p = pivot(a, start, stop, ulimit, llimit);
            quicksort(a, start, p, a[p], llimit);
            quicksort(a, p+1, stop, ulimit, a[p]);
        }
    }

    // Write pre-conditions for this method.
    //@ modifies a[*];
    //@ requires start >= 0 && start < stop;
    //@ requires stop >= start && stop <= a.length;
    // Write post-conditions for this method.
    //@ ensures \result >= start && \result <= stop;
    private static int pivot(int[] a, int start, int stop, int ulimit, int llimit)
    {
        int p = partition(a, a[start], start+1, stop, ulimit, llimit);
        if (start < p)
            swap(a, start, p);
        return p;
    }

    // Write pre-conditions for this method.
    //@ modifies a[*];
    //@ requires a != null && a.length > 0;
    //@ requires \typeof(pivot) <: \type(int);
    //@ requires start >= 0;
    //@ requires stop <= a.length;
    // Write post-conditions for this method.
    // ensures \result >= 0 && \result < a.length;
    private static int partition(int[] a, int pivot, int start, int stop, int ulimit, int llimit)
    {
        if (start >= stop) 
            return start - 1;
        if (a[start] < pivot)
            return partition(a, pivot, start + 1, stop, ulimit, llimit);
        if (a[--stop] > pivot)
            return partition(a, pivot, start, stop, ulimit, llimit);
        if (start < stop) {
            swap(a, start, stop);
            return partition(a, pivot, start+1, stop, ulimit, llimit);
        } else
            return start;
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
