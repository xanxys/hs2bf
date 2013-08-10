#include <stdio.h>
#include <stdlib.h>

#define MEM_SIZE (20*1000*1000) // 20MB


void run(FILE *log,char *code){
    char *code_base=code;
    
    unsigned char *ptr_base=malloc(MEM_SIZE);
    memset(ptr_base,0,MEM_SIZE);
    
    unsigned char *ptr=ptr_base;
    
    long stp=0;
    while(*code){
        /*
        if(log)
            fprintf(log,"%c %d %d\n",*code,code-code_base,ptr-ptr_base);
        */
        stp++;
        switch(*code){
            case '>': ++ptr; break;
            case '<': --ptr; break;
            case '+': ++*ptr; break;
            case '-': --*ptr; break;
            case '.': fwrite(ptr,1,1,stdout); break;
            case ',': fread(ptr,1,1,stdin); break;
            case '[':
                if(*ptr==0){
                    int c=1;
                    while(c>0){
                        code++;
                        if(*code=='[') c++;
                        if(*code==']') c--;
                    }
                }
                break;
            case ']':
                if(*ptr!=0){
                    int c=1;
                    while(c>0){
                        code--;
                        if(*code==']') c++;
                        if(*code=='[') c--;
                    }
                }
            default:
                stp--;
        }
        
        code++;
    }
    fprintf(stderr,"%lld steps\n",stp);
    
    free(ptr_base);
}

int main(int argc,char **argv){
    if(argc!=2 && argc!=3){
        printf("usage: bfi <file> (compiled with MEM_SIZE=%d)\n",MEM_SIZE);
        printf("usage: bfi <file> <prof> (compiled with MEM_SIZE=%d)\n",MEM_SIZE);
        return -1;
    }
    
    // open
    FILE *fp=fopen(argv[1],"r");
    if(fp==NULL){
        printf("could not open %s\n",argv[1]);
        return -2;
    }
    
    fseek(fp,0,SEEK_END);
    int size=ftell(fp);
    fseek(fp,0,SEEK_SET);
    
    char *code=malloc(size+1);
    fread(code,size,1,fp);
    code[size]=0;
    
    // close
    fclose(fp);
    
    setbuf(stdin,NULL);
    setbuf(stdout,NULL);
    fflush(stdin);
    fflush(stdout);
    
    // open optional log file
    FILE *log=NULL;
    if(argc==3){
        log=fopen(argv[2],"w");
        if(log==NULL){
            printf("could not open %s\n",argv[2]);
            return -2;
        }
    }
    
    run(log,code);
    free(code);
    if(log) fclose(log);
    
    return 0;
}

