#include <stdio.h>
#include <stdlib.h>

int main() {


    int size = 4;
    char *ptr = (char *)malloc(size);

    for (int i = 0; i < size; i++) {
        ptr[i] = 'A' + i;
    }
    ptr[size - 1] = '\0';

    //printf("%s\n", ptr);
    for (int i = 0; i < size; i++) {
        printf("ptr[%d] = %c\n", i, ptr[i]);
    }

    free(ptr);

    return 0;
}
