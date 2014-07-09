/*
*   Name: Fusheng Yuan
*   Andrew ID: fyuan
*/
/* 
 * trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(int M, int N, int A[N][M], int B[M][N]);
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 1KB direct mapped cache with a block size of 32 bytes.
 */ 
#include <stdio.h>
#include "cachelab.h"
#include "contracts.h"

int is_transpose(int M, int N, int A[N][M], int B[M][N]);

/* 
 * transpose_submit - This is the solution transpose function that you
 *     will be graded on for Part B of the assignment. Do not change
 *     the description string "Transpose submission", as the driver
 *     searches for that string to identify the transpose function to
 *     be graded. The REQUIRES and ENSURES from 15-122 are included
 *     for your convenience. They can be removed if you like.
 */
char transpose_submit_desc[] = "Transpose submission";
void transpose_submit(int M, int N, int A[N][M], int B[M][N])
{
    int i, j, row, col;
    int tmp7, tmp0, tmp1, tmp2;
    int tmp3, tmp4, tmp5, tmp6; 
    if(M == 32){
        for(row = 0; row < 32; row += 8){
            for(col = 0; col < 32; col += 8){
                for(i = row; i < row + 8; i++){
                    for(j = col; j < col + 8; j++){
                        if(i != j){
                            tmp0 = A[i][j];
                            B[j][i] = tmp0;
                        }
                    }
                    if(col == row){
                        tmp0 = A[i][i];
                        B[i][i] = tmp0;
                    }
                }
            }
        }
    }else if (N == 64) {
        for (row = 0; row < 64; row = row + 8){
            for (col = 0; col < 64; col = col + 8){
                for (i = col; i < col + 4; i++){
                        tmp0 = A[i][row];
                        tmp1 = A[i][row+1];
                        tmp2 = A[i][row+2];
                        tmp3 = A[i][row+3];
                        tmp4 = A[i][row+4];
                        tmp5 = A[i][row+5];
                        tmp6 = A[i][row+6];
                        tmp7 = A[i][row+7];
                    if(col + 8 < 63){
                        B[row][i+8] = tmp0;
                        B[row+1][i+8] = tmp1;
                        B[row+2][i+8] = tmp2;
                        B[row+3][i+8] = tmp3;
                        B[row][i+12] = tmp4;
                        B[row+1][i+12] = tmp5;
                        B[row+2][i+12] = tmp6;
                        B[row+3][i+12] = tmp7;
                    }else{
                        B[row][i] = tmp0;
                        B[row+1][i] = tmp1;
                        B[row+2][i] = tmp2;
                        B[row+3][i] = tmp3;
                        B[row][i+4] = tmp4;
                        B[row+1][i+4] = tmp5;
                        B[row+2][i+4] = tmp6;
                        B[row+3][i+4] = tmp7;
                    }
                }
                for (i = row; i < row + 4; i++){
                    if(col + 8 < 63){
                        tmp4 = A[col+4][i];
                        tmp5 = A[col+5][i];
                        tmp6 = A[col+6][i];
                        tmp7 = A[col+7][i];
                        B[i][col+4] = tmp4;
                        B[i][col+5] = tmp5;
                        B[i][col+6] = tmp6;
                        B[i][col+7] = tmp7;
                    }else{
                        tmp4 = A[col+4][i];
                        tmp5 = A[col+5][i];
                        tmp6 = A[col+6][i];
                        tmp7 = A[col+7][i];
                        tmp0 = B[i][col+4];
                        tmp1 = B[i][col+5];
                        tmp2 = B[i][col+6];
                        tmp3 = B[i][col+7];
                        B[i][col+4] = tmp4;
                        B[i][col+5] = tmp5;
                        B[i][col+6] = tmp6;
                        B[i][col+7] = tmp7;
                        B[i+4][col] = tmp0;
                        B[i+4][col+1] = tmp1;
                        B[i+4][col+2] = tmp2;
                        B[i+4][col+3] = tmp3;
                    }
                }
                if(col + 8 < 63){
                    for (i = row; i < row + 4; i++){
                        tmp0 = B[i][col+8];
                        tmp1 = B[i][col+9];
                        tmp2 = B[i][col+10];
                        tmp3 = B[i][col+11];
                        tmp4 = B[i][col+12];
                        tmp5 = B[i][col+13];
                        tmp6 = B[i][col+14];
                        tmp7 = B[i][col+15];
                        B[i][col] = tmp0;
                        B[i][col+1] = tmp1;
                        B[i][col+2] = tmp2;
                        B[i][col+3] = tmp3;
                        B[i+4][col] = tmp4;
                        B[i+4][col+1] = tmp5;
                        B[i+4][col+2] = tmp6;
                        B[i+4][col+3] = tmp7;
                    }
                }
                for (i = row + 4; i < row + 8; i ++){
                     tmp0 = A[col+4][i];
                     tmp1 = A[col+5][i];
                     tmp2 = A[col+6][i];
                     tmp3 = A[col+7][i];
                     B[i][col+4] = tmp0;
                     B[i][col+5] = tmp1;
                     B[i][col+6] = tmp2;
                     B[i][col+7] = tmp3;
                }
            }
        }
    }else if (M == 61) {
        for (row = 0; row < N; row += 17) {
            for (col = 0; col < M; col += 17) {
                for (i = row; i < row + 17 && i < N; i++) {
                    for (j = col; j < col + 17 && j < M; j++){
                        tmp0 = A[i][j];
                        B[j][i] = tmp0;
                    }
                }
            }
        }
    }else{
        for (i = 0; i < N; i++) {
            for (j = 0; j < M; j++) {
                tmp0 = A[i][j];
                B[j][i] = tmp0;
            }
        }
    }

    ENSURES(is_transpose(M, N, A, B));
    
}

/* 
 * You can define additional transpose functions below. We've defined
 * a simple one below to help you get started. 
 */ 

/* 
 * trans - A simple baseline transpose function, not optimized for the cache.
 */
char trans_desc[] = "Simple row-wise scan transpose";
void trans(int M, int N, int A[N][M], int B[M][N])
{
    int i, j, tmp;

    REQUIRES(M > 0);
    REQUIRES(N > 0);

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; j++) {
            tmp = A[i][j];
            B[j][i] = tmp;
        }
    }    

    ENSURES(is_transpose(M, N, A, B));
}

/*
 * registerFunctions - This function registers your transpose
 *     functions with the driver.  At runtime, the driver will
 *     evaluate each of the registered functions and summarize their
 *     performance. This is a handy way to experiment with different
 *     transpose strategies.
 */
void registerFunctions()
{
    /* Register your solution function */
    registerTransFunction(transpose_submit, transpose_submit_desc); 

    /* Register any additional transpose functions */
    registerTransFunction(trans, trans_desc); 

}

/* 
 * is_transpose - This helper function checks if B is the transpose of
 *     A. You can check the correctness of your transpose by calling
 *     it before returning from the transpose function.
 */
int is_transpose(int M, int N, int A[N][M], int B[M][N])
{
    int i, j;

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; ++j) {
            if (A[i][j] != B[j][i]) {
                return 0;
            }
        }
    }
    return 1;
}

