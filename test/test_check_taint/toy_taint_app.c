#include <stdio.h>
#include <unistd.h>
#include <signal.h>
#include <stdlib.h>
#include <stdarg.h>

/* Read int from file 1, file 2, add ints, then close files.  
 * Each should cause migration*/ 

#define FILE1 "tainted_int.txt" // tainted data
#define FILE2 "public_int.txt" // public data

void send_pin_print_sequence() {
    // signal declassify sequence
    asm volatile ("ud2");
    //send pointer to length
    asm volatile ("emms");
}
void send_pin_check_sequence(unsigned long length, int * data) {
    printf("data to check at %p\n", data);
    // signal declassify sequence
    asm volatile ("ud2");
    //send pointer to length
    asm volatile ("fxsave %0  \n"
            :
            : "m" (length)
            :
        );
    //send pointer to the data
    asm volatile ("ldmxcsr %0  \n"
            :
            : "m" (*data)
            :
        );
}
void send_pin_declassify_sequence(unsigned long length, unsigned *data) {

    // signal declassify sequence
    asm volatile ("ud2");
    //send pointer to length
    asm volatile ("fxsave %0  \n"
            :
            : "m" (length)
            :
        );
    //send pointer to the data
    asm volatile ("fxrstor %0  \n"
            :
            : "m" (*data)
            :
        );
}

int tainted_int;
int sum;
int main(){
    FILE *tainted_file, *public_file;
    int public_int, ret;
    
    printf("Start of program, about to open private file\n");
    //open tainted file and read int
    tainted_file = fopen(FILE1, "r");
    if(!tainted_file){
        perror("Error opening tainted file");
        exit(-1);
    }
    ret = fscanf(tainted_file, "%d", &tainted_int);
    if (ret != 1){
        printf("Error reading int from %s\n", FILE1);
        exit(-1);
    }
    printf("Read in %d from %s\n", tainted_int, FILE1);
    
    //open public file and read int
    public_file = fopen(FILE2, "r");
    if(fscanf(public_file, "%d", &public_int) != 1){
        printf("Error reading int from %s\n", FILE2);
        exit(-1);
    }
    //printf("Read in %d from %s\n", public_int, FILE2);

    sum = tainted_int + public_int;
    //printf("Sum of two ints is %d\n", sum);

    //check taints
    send_pin_print_sequence();
    send_pin_check_sequence(sizeof(tainted_int), &tainted_int);
    send_pin_check_sequence(sizeof(public_int), &public_int);
    send_pin_check_sequence(sizeof(sum), &sum);
    send_pin_declassify_sequence(sizeof(sum), &sum);
    send_pin_check_sequence(sizeof(sum), &sum);
    send_pin_print_sequence();
    printf("tainted_int: %p public_int: %p, sum: %p\n",
            &tainted_int, &public_int, &sum);

    fclose(tainted_file);
    printf("Closed %s\n", FILE1);

    fclose(public_file);
    printf("Closed %s\n", FILE2);

    exit(0);
    //return (0);
}
