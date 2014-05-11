#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

// 20MB
const int MEM_SIZE = 20*1000*1000;


void run(const std::string& code_memory) {
    std::vector<unsigned char> data_memory(MEM_SIZE, 0);
    
    unsigned char* ptr = data_memory.data();
    const char* ptr_program = code_memory.data();
    const char* const ptr_program_end = code_memory.data() + code_memory.size();

    uint64_t steps = 0;
    while(ptr_program < ptr_program_end) {
        steps++;
        switch(*ptr_program){
            case '>': ++ptr; break;
            case '<': --ptr; break;
            case '+': ++*ptr; break;
            case '-': --*ptr; break;
            case '.': std::cout << std::unitbuf << *ptr; break;
            // TODO: do disable stdin buffering.
            case ',': *ptr = std::cin.get(); break;
            case '[':
                if(*ptr==0){
                    int c=1;
                    while(c>0){
                        ptr_program++;
                        if(*ptr_program=='[') c++;
                        if(*ptr_program==']') c--;
                    }
                }
                break;
            case ']':
                if(*ptr!=0){
                    int c=1;
                    while(c>0){
                        ptr_program--;
                        if(*ptr_program==']') c++;
                        if(*ptr_program=='[') c--;
                    }
                }
            default:
                steps--;
        }
        
        ptr_program++;
    }
    std::cerr << steps << " steps" << std::endl;
}

int main(int argc, char** argv) {
    // Parse argument
    if(argc != 2) {
        std::cout << "bfi (compiled with MEM_SIZE=" << MEM_SIZE << ")" << std::endl;
        std::cout << "usage: bfi <file>" << std::endl;
        return -1;
    }
    const std::string bf_code_path(argv[1]);
    
    // Read bf code.
    std::ifstream bf_code_file(bf_code_path);
    if(!bf_code_file.is_open()) {
        std::cout << "could not open " << bf_code_path << std::endl;
        return -2;
    }

    const std::string bf_code(
        (std::istreambuf_iterator<char>(bf_code_file)),
        std::istreambuf_iterator<char>());
    
    run(bf_code);
    return 0;
}
