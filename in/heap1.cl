    int[10] heap ;
    int size=0;
    for(int ii=0;ii<N;ii++){
      int x=data[ii];
      //data to insert
      int i=size;
      heap[i]=x;
      size++;
      while( i > 0 ){
        int j=(i-1) / 2; // parent
        int xj=heap[j], xi=heap[i];
        if(xj<xi)break;
        heap[i]=xj; heap[j]=xi;
        i=j;
      }
    }
