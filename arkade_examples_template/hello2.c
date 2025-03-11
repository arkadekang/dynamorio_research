#include <stdio.h>
#include <stdlib.h>

char* allocate_memory(int size) {
    char *ptr = (char *)malloc(size);
    //if (ptr == NULL) {
    //    printf("Memory allocation failed\n");
    //    exit(1);
    //}
    return ptr;
}

int main() {
    int size = 4;
    char *ptr = allocate_memory(size);

    for (int i = 0; i < size; i++) {
        ptr[i] = 'A' + i;
    }
    ptr[size - 1] = '\0';

    //for (int i = 0; i < size; i++) {
    //    printf("ptr[%d] = %c\n", i, ptr[i]);
    //}

    free(ptr);

    return 0;
}
