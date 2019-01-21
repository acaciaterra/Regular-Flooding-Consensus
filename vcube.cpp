/*
=============================================================================
Codigo fonte: implementacao consenso regular por inundacao com V-Cube.
Autora: Acacia dos Campos da Terra
Orientador: Prof. Elias P. Duarte Jr.
=============================================================================
*/

/*--------bibliotecas--------*/
#include <stdio.h>
#include <stdlib.h>
#include "smpl.h"
#include <set>
#include <string>
#include <vector>
#include <algorithm>
#include <iostream>
#include <memory>

/*--------eventos--------*/
#define test 1
#define fault 2
#define repair 3
#define brcast_dec 4
#define receive_ack 5
#define broadcast 6
#define new_msg 7
#define propose 8
#define receive_ack_dec 9
#define broadcast_round 10
#define receive_ack_round 11

/*--------definicoes usadas pela funcao cisj--------*/
#define POW_2(num) (1<<(num)) //equivale a 2 elevado a num (sendo num o tamanho dos clusters)
#define VALID_J(j, s) ((POW_2(s-1)) >= j) //verifica se j eh um indice valido para acessar no cluster

/*--------estrutura das mensagens(tree e ack)--------*/
typedef struct {
	char type; //2 tipos: tree e ack (T e A)
	std:: string m; //mensagem m
	int idorigem; //id da origem
	int timestamp; //contador sequencial
}tmsg;
std:: vector<tmsg> mensagens;

//ultima mensagem utilizada pelo programa (para enviar/receber)
// auto ultima_msg = std::make_unique<tmsg>();
std::vector <tmsg> msg_propose;
std::vector <tmsg> msg_decide;
std::vector <tmsg> msg_round;

std::vector <int> ultimo_nodo;
std::vector <int> ultimo_nodo_dec;
std::vector <int> ultimo_nodo_round;

/*--------estrutura da tripla armazenada pelo ack_set--------*/
struct tset{
	int idorigem, iddestino;
	tmsg m;

	bool operator<(const tset &outro) const{
		if(idorigem < outro.idorigem)
			return true;
		if(outro.idorigem < idorigem)
			return false;
		if(iddestino < outro.iddestino)
			return true;
		if(outro.iddestino < iddestino)
			return false;
		return m.m < outro.m.m;
	}
};

/*--------descritor do nodo--------*/
typedef struct{
	int id; //cada nodo tem um id
	int idr; //id real!!!
	int *state; //vetor state do nodo
	std:: vector<tmsg> last; //vetor com a ultima mensagem recebida de cada processo fonte
	std:: set<tset> ack_set; //set de tset
	std:: vector<std:: vector<int>> correct_this_round; //armazena quais processos estavam sem-falha na rodada
	//a matriz correct_this_round vai ter o como size() N, o numero maximo de rodadas
	//e a segunda coordenada da matriz tera como size a quantidade de nodos sem-falha na rodada da primeira coordenada
	//em cada posicao tera um identificador de nodo (de 0 a N) sem-falha
	std:: vector<std:: vector<int>> proposal_set; //armazena as propostas recebidas em cada rodada (mesmo esquema do anterior)
	int decided;
}tnodo;
std:: vector<tnodo> nodo;

/*--------estrutura do vetor de testes--------*/
typedef struct{
	int *vector; //cada nodo retornara um vetor de inteiros
	int size; //tamanho do vetor
	int *etapa;//o s da funcao cis
} testsvector;
testsvector *tests;

/*--------estrutura usada pela funcao cisj--------*/
typedef struct node_set {
	int* nodes;
	ssize_t size;
	ssize_t offset;
} node_set;

int token, N, timestamp = 0, s, rodada = 1, nodo_token;
/*--------funcoes usadas pelo cisj--------*/
static node_set*
set_new(ssize_t size)
{
	node_set* newn;

	newn = (node_set*)malloc(sizeof(node_set));
	newn->nodes = (int*)malloc(sizeof(int)*size);
	newn->size = size;
	newn->offset = 0;
	return newn;
}

static void
set_insert(node_set* nodes, int node)
{
	if (nodes == NULL) return;
	nodes->nodes[nodes->offset++] = node;
}

static void
set_merge(node_set* dest, node_set* source)
{
	if (dest == NULL || source == NULL) return;
	memcpy(&(dest->nodes[dest->offset]), source->nodes, sizeof(int)*source->size);
	dest->offset += source->size;
}

static void
set_free(node_set* nodes)
{
	free(nodes->nodes);
	free(nodes);
}
/* node_set.h --| */

node_set*
cis(int i, int s)
{
	node_set* nodes, *other_nodes;
	int xorr = i ^ POW_2(s-1);
	int j;

	/* starting node list */
	nodes = set_new(POW_2(s-1));

	/* inserting the first value (i XOR 2^^(s-1)) */
	set_insert(nodes, xorr);

	/* recursion */
	for (j=1; j<=s-1; j++) {
		other_nodes = cis(xorr, j);
		set_merge(nodes, other_nodes);
		set_free(other_nodes);
	}
	return nodes;
}
/*--------fim das funcoes do cisj--------*/


/*--------funcao que encontra qual sera o nodo testador--------*/
//nesta funcao sao encontrados os testadores de cada nodo
//(primeiro nodo SEM-FALHA de cada cluster em cada etapa)
int findtester (int i, int s) {
	int aux = 0;
	node_set* cluster = cis(i, s);
	// printf("---------> i: %d s: %d cluster: %d\n", i, s, cluster->offset);
	for(int j = 0; j < cluster->size; j++){ //for para percorrer todo o cluster
		if(status(nodo[cluster->nodes[j]].id) == 0){//verifica se o nodo encontrado eh sem-falha
			//ira retornar o primeiro do cluster que esta SEM-FALHA
			aux = cluster->nodes[j];
			free(cluster); //libera a memoria
			return aux;
		}
	}
	//se acabar o for, eh porque todos os nodos do cluster estao falhos
	free(cluster);
	return -2;
}


/*--------funcao que retorna os testes que serao executados pelo nodo--------*/
testsvector* testes(int n, int s, std:: vector<tnodo> &nodo) {
	//n = numero de nodos
	//s = log de n (numero de rodadas de teste [cada linha da tabela])

	int nodoTestador, position = 0;
	testsvector *tests = (testsvector*) malloc(sizeof(testsvector)*n);

	for(int k = 0; k < n; k++){
		tests[k].vector = (int*) malloc(sizeof(int)*n);//aloca o vetor com n posicoes
		tests[k].etapa = (int*) malloc(sizeof(int)*n);
		if(status(nodo[k].id) == 1) {
			tests[k].size = 0;
			continue;
		}//se for falho, nao faz a busca por testadores

		for(int i = 0; i < n; i++){ //for que percorre todos os nodos
			for(int j = 1; j <= s; j++){ //for para percorrer todas as etapas
				nodoTestador = findtester(i, j); //encontra testador do nodo

				//se o nodo for igual a k, entao adiciona a lista de testadores daquele nodo
				//significa que eh o testador que estamos procurando
				if(nodoTestador == k){
					// printf(">>>>> %d\n", j);
					tests[k].vector[position] = i;
					tests[k].etapa[position++] = j;
				}
			}
		}
		tests[k].size = position;
		position = 0;
	}
	return tests; //retorna o vetor com os testes executados
}
/*------------funcoes do broadcast-----------------*/

//funcao para checar os acks
void checkacks(tnodo j, tmsg msg, int flag){
	//flag: se 1, eh decisao, se 2 eh propose, se 3 eh troca de round (ainda nao decidiu)
	bool r;
	//existe algum elemento em ack_set que respeite <j, *, m>?
	//retorna true, caso exista
	r = std::any_of(nodo[token].ack_set.begin(), nodo[token].ack_set.end(), [j, msg] (auto const &elem){
		return elem.idorigem == j.idr && !(elem.m.m.compare(msg.m));
	});
	//if ack_set intersec {<j, *, m>} = vazio
	if(!r){
		// printf("Acabaram os acks pendentes do processo\n");
		//veririca se source(m) esta sem-falha e tambem o j para mim (i)
		if(nodo[token].state[msg.idorigem] % 2 == 0 && nodo[token].state[j.id] % 2 == 0){
			// send_ack(msg, j); //enviando ack para pj
			if(flag == 1){
				ultimo_nodo[j.idr] = token;
				schedule(receive_ack_dec, 1.0, j.idr);
			}
			else if(flag == 2){
				ultimo_nodo_dec[j.idr] = token;
				schedule(receive_ack, 1.0, j.idr);
			}
			else {
				ultimo_nodo_round[j.idr] = token;
				schedule(receive_ack_round, 1.0, j.idr);
			}
		}
	}
}

void print_tests(){
	for(int j = 0; j < N; j++){
		for(int i = 0; i < tests[j].size; i++){
			printf("> %d (s: %d) ", tests[j].vector[i], tests[j].etapa[i]);
		}
		printf("\n");
	}
}

//funcao que verificara se no meu correct_this_round ja estao todos os nodos sem-falha
//entao podera decidir
void verify (int recebeu){
	int n, tamp;
	bool resver, result;
	printf("Correct this round na rodada %d para o nodo %d: \n", rodada, recebeu);
	for(int i = 0; i < nodo[recebeu].correct_this_round[rodada].size(); i++){
		printf("%d ", nodo[recebeu].correct_this_round[rodada][i]);
	}
	printf("\n");
	for(int i = 0; i < N; i++){
		// printf("N:::::::::::::::::: %d\n", N);
		// printf("Analisando o nodo %d...\n", i);
		if(nodo[recebeu].state[i] % 2 == 0){
			// printf("Nodo %d esta sem falha para o nodo %d\n", i, recebeu);
			//o nodo esta sem-falha no state
			//precisa estar em correct_this_round tambem
			//existe o nodo i no correct_this_round?
			//retorna true, caso exista
			// printf("AAAAAAAAAAAAAA %d\n", val);
			resver = std::any_of(nodo[recebeu].correct_this_round[rodada].begin(), nodo[recebeu].correct_this_round[rodada].end(), [i] (auto const &elem){
				return elem == i;
			});

			if(!resver){
				//se nao existe, nem tem porque estar na funcao
				// printf("Encerrando a funcao pq o nodo %d nao existe no ctr\n", i);
				return;
			}
		}
	}
	//terminou o for, entao quer dizer que todos os nodos corretos estao em correct_this_round
	//se ainda nao decidiu
	if(nodo[recebeu].decided == -1){
		// printf("Chegou nessa coisa\n");
		//verifica se o correct_this_round esta igual na rodada anterior
		//ordenar para ter certeza que é igual
		std::sort(nodo[recebeu].correct_this_round[rodada].begin(), nodo[recebeu].correct_this_round[rodada].end());
		std::sort(nodo[recebeu].correct_this_round[rodada-1].begin(), nodo[recebeu].correct_this_round[rodada-1].end());
		std::sort(nodo[recebeu].proposal_set[rodada].begin(), nodo[recebeu].proposal_set[rodada].end());

		result = std::equal(nodo[recebeu].correct_this_round[rodada].begin(), nodo[recebeu].correct_this_round[rodada].end(),
		nodo[recebeu].correct_this_round[rodada-1].begin());

		// printf("Correct this round na rodada %d: \n", rodada);
		// for(int i = 0; i < nodo[recebeu].correct_this_round[rodada].size(); i++){
		// 	printf("%d ", nodo[recebeu].correct_this_round[rodada][i]);
		// }
		// printf("\n");
		//
		// printf("Correct this round na rodada %d: \n", rodada-1);
		// for(int i = 0; i < nodo[recebeu].correct_this_round[rodada-1].size(); i++){
		// 	printf("%d ", nodo[recebeu].correct_this_round[rodada-1][i]);
		// }
		printf("\n");

		if(result){
			//os vetores sao iguais, entao pode decidir
			printf("Vetores iguais\n");
			nodo[recebeu].decided = nodo[recebeu].proposal_set[rodada][0];
			printf("**** O nodo %d vai decidir pelo valor %d\n", recebeu, nodo[recebeu].decided);
			//fazer broadcast da decisao

			//armazena em mensagens todas as mensagens ja enviadas pelo broadcast,
			//contendo o id de origem e o timestamp (unico para cada mensagem)
			//--- transforma a string em um tmsg ---
			mensagens.push_back(tmsg{'T', "decid " + std::to_string(nodo[recebeu].decided), nodo[recebeu].idr, timestamp});
			tamp = mensagens.size()-1;
			// std::cout << "Mensagem armazenada::::::::::::::::::" << mensagens[mensagens.size()-1].m << "\n";

			msg_decide[recebeu].type = mensagens[tamp].type;
			msg_decide[recebeu].m.assign(mensagens[tamp].m);
			msg_decide[recebeu].idorigem = mensagens[tamp].idorigem;
			msg_decide[recebeu].timestamp = mensagens[tamp].timestamp;

			// rodada = 0;
			nodo_token = recebeu;
			//incrementa o timestamp sempre que gera uma nova mensagem
			timestamp++;
			schedule(brcast_dec, 0.1, recebeu);
		} else {
			// rodada++;

			//armazena em mensagens todas as mensagens ja enviadas pelo broadcast,
			//contendo o id de origem e o timestamp (unico para cada mensagem)
			//--- transforma a string em um tmsg ---
			//myseT é quando devo usar proposal_set-1 na hora do deliver!!!!!!!!
			mensagens.push_back(tmsg{'T', "myseT rodada: "+ std:: to_string(rodada + 1) + " token: " + std::to_string(recebeu), nodo[recebeu].idr, timestamp});
			tamp = mensagens.size()-1;
			// std::cout << "Mensagem armazenada::::::::::::::::::" << mensagens[mensagens.size()-1].m << "\n";

			msg_round[recebeu].type = mensagens[tamp].type;
			msg_round[recebeu].m.assign(mensagens[tamp].m);
			msg_round[recebeu].idorigem = mensagens[tamp].idorigem;
			msg_round[recebeu].timestamp = mensagens[tamp].timestamp;

			// rodada = 0;
			nodo_token = recebeu;
			//incrementa o timestamp sempre que gera uma nova mensagem
			timestamp++;
			schedule(broadcast_round, 0.1, recebeu);

		}
		// if (nodo[recebeu].correct_this_round[rodada].size() == nodo[recebeu].correct_this_round[rodada-1].size()){
		// 	for(int i = 0; i < nodo[recebeu].correct_this_round[rodada].size(); i++){
		// 		if(nodo[recebeu].correct_this_round[rodada][i] != nodo[recebeu].correct_this_round[rodada-1][i]){
		//
		// 		}
		// 	}
		// }
	}
}

void freceive_round(int enviou, int recebeu){
	int k, etp, val, tamp;
	bool res, rescon;
	std::string comp("strin");
	if(nodo[recebeu].last[msg_round[enviou].idorigem].type == 'N'
	|| msg_round[enviou].timestamp > nodo[recebeu].last[msg_round[enviou].idorigem].timestamp){
		//last_i[source(m)] <- m
		//Atualiza o last do nodo atual com a mensagem que acabou
		//de ser recebida do outro nodo
		nodo[recebeu].last[msg_round[enviou].idorigem].type = msg_round[enviou].type;
		nodo[recebeu].last[msg_round[enviou].idorigem].m.assign(msg_round[enviou].m);
		nodo[recebeu].last[msg_round[enviou].idorigem].idorigem = msg_round[enviou].idorigem;
		nodo[recebeu].last[msg_round[enviou].idorigem].timestamp = msg_round[enviou].timestamp;

		msg_round[recebeu].type = msg_round[enviou].type;
		msg_round[recebeu].m.assign(msg_round[enviou].m);
		msg_round[recebeu].idorigem = msg_round[enviou].idorigem;
		msg_round[recebeu].timestamp = msg_round[enviou].timestamp;

		//deliver(m)
		std::cout <<"[DELIVER] mensagem \"" << nodo[recebeu].last[msg_round[enviou].idorigem].m << "\" recebida do nodo " << enviou <<" foi entregue para a aplicacao pelo processo " << recebeu << " no tempo {" << time() << "}\n\n";

		for(int i = 0; i < 5; i++){
			//copia os primeiros 5 caracteres da mensagem recebida, para saber se
			//foi brcast de decisao ou de propose
			comp[i] = nodo[recebeu].last[msg_round[enviou].idorigem].m[i];
			// std::cout << "-----------------" << comp[i] << "\n";
		}

		if(comp == "myset" || comp == "myseT"){
			//quando faz deliver do brcast de propose, atualiza os vetores do consenso

			// nodo[recebeu].correct_this_round[rodada].push_back(msg_round[enviou].idorigem);

			// std::cout << comp << "\n";
			for(int i = 0; i < nodo[recebeu].correct_this_round[rodada - 1].size(); i++)
				nodo[recebeu].correct_this_round[rodada].push_back(nodo[recebeu].correct_this_round[rodada - 1][i]);

			//unir o meu proposal_set com o de quem me enviou
			//percorrer o proposal_set de quem enviou, verificando se já tem no de quem recebeu
			//ou nao, se nao tiver entao adiciona
			for(int contador = 0; contador < nodo[enviou].proposal_set[rodada - 1].size(); contador++){
				//existe algum o valor do proposal_set de quem enviou no proposal_set de quem recebeu?
				//retorna true, caso exista
				val = nodo[enviou].proposal_set[rodada - 1][contador];
				// printf("AAAAAAAAAAAAAA %d\n", val);
				rescon = std::any_of(nodo[recebeu].proposal_set[rodada].begin(), nodo[recebeu].proposal_set[rodada].end(), [val] (auto const &elem){
					return elem == val;
				});

				if(!rescon){
					// printf("%d - nao existe no meu proposal_set (%d)\n", recebeu, val);
					//adiciona o valor ao meu proposal_set, pois acabei de recebe-lo
					nodo[recebeu].proposal_set[rodada].push_back(val);
					// printf(">>>>>>>>>>>>>> %d\n", val);
				}
			}
			// printf("Tinha que chamar a verify\n");
			verify(recebeu);
		}
		/*
		else if(comp == "decid"){
			//quando faz brcast de decisao, apenas propaga a decisao para os outros nodos
			//mas apenas se pi esta correto e ainda nao decidiu
			if(status(nodo[recebeu].id == 0) && nodo[recebeu].decided == -1){
				nodo[recebeu].decided = nodo[enviou].decided;
				// printf("##### nodo %d decidiu pelo valor %d, recebido do nodo %d\n", recebeu, nodo[recebeu].decided, enviou);

				//armazena em mensagens todas as mensagens ja enviadas pelo broadcast,
				//contendo o id de origem e o timestamp (unico para cada mensagem)
				//--- transforma a string em um tmsg ---
				mensagens.push_back(tmsg{'T', "decid " + std::to_string(nodo[recebeu].decided), nodo[recebeu].idr, timestamp});
				tamp = mensagens.size()-1;
				// std::cout << "Mensagem armazenada::::::::::::::::::" << mensagens[mensagens.size()-1].m << "\n";

				// rodada = 0;
				nodo_token = recebeu;
				//incrementa o timestamp sempre que gera uma nova mensagem
				timestamp++;
				schedule(broadcast, 0.1, recebeu);
			}
		}
		*/

		if(status(nodo[msg_round[enviou].idorigem].id) != 0){
			// std::cout <<"Fazendo novo broadcast para os vizinhos sem-falha... " << "\n";
			schedule(broadcast, 0.1, recebeu);
			return;
		}
	}
	//encontrar identificador do cluster s de i que contem j
	for(int c = 0; c < tests[recebeu].size; c++){
		// printf("Agora vai calcular o cluster...\n");
		if(tests[recebeu].vector[c] == enviou){
			etp = tests[recebeu].etapa[c];
			// printf("Cluster do %d para o %d: %d\n", recebeu, enviou, etp);
			break;
		}
	}
	// print_tests();
	//retransmitir aos vizinhos corretos na arvore de source(m)
	//que pertencem ao cluster s que contém elementos
	//corretos de g

	for(int i = 0; i < N; i ++){
		for(int j = 0; j < tests[i].size; j++){
			for(int k = 1; k <= etp - 1; k++){
				if(tests[i].vector[j] == recebeu && tests[i].etapa[j] == k && status(nodo[i].id) == 0){
					// existe algum elemento em ack_set que respeite <j, k, m>?
					//retorna true, caso exista
					res = std::any_of(nodo[recebeu].ack_set.begin(), nodo[recebeu].ack_set.end(), [i, enviou] (auto const &elem){
						return elem.idorigem == enviou && elem.iddestino == nodo[i].idr && !(elem.m.m.compare(msg_round[enviou].m));
					});
					//if <j,k,m> nao pertence ack_set(i)
					// j = enviou, k = ff_neighbor (aqui eh o nodo[i])
					if(!res){
						nodo[recebeu].ack_set.insert(tset{enviou, nodo[i].idr, msg_round[enviou]});
						printf("[RBCAST] processo %d envia mensagem para processo %d\n", recebeu, nodo[i].idr);
						freceive_round(recebeu, nodo[i].idr);
					}
				}
			}
		}
	}
	checkacks(nodo[enviou], msg_round[enviou], 3);
}


void freceive_dec(int enviou, int recebeu){
	int k, etp, val, tamp;
	bool res, rescon;
	std::string comp("strin");
	// printf("Timestamp da mensagem que acabei de receber: %d\n", msg_decide[enviou].timestamp);
	// printf("Timestamp da mensagem ultima mensagem que recebi: %d\n", nodo[recebeu].last[msg_decide[enviou].idorigem].timestamp);

	if(nodo[recebeu].last[msg_decide[enviou].idorigem].type == 'N'
	|| msg_decide[enviou].timestamp > nodo[recebeu].last[msg_decide[enviou].idorigem].timestamp){
		//last_i[source(m)] <- m
		//Atualiza o last do nodo atual com a mensagem que acabou
		//de ser recebida do outro nodo
		nodo[recebeu].last[msg_decide[enviou].idorigem].type = msg_decide[enviou].type;
		nodo[recebeu].last[msg_decide[enviou].idorigem].m.assign(msg_decide[enviou].m);
		nodo[recebeu].last[msg_decide[enviou].idorigem].idorigem = msg_decide[enviou].idorigem;
		nodo[recebeu].last[msg_decide[enviou].idorigem].timestamp = msg_decide[enviou].timestamp;

		msg_decide[recebeu].type = msg_decide[enviou].type;
		msg_decide[recebeu].m.assign(msg_decide[enviou].m);
		msg_decide[recebeu].idorigem = msg_decide[enviou].idorigem;
		msg_decide[recebeu].timestamp = msg_decide[enviou].timestamp;

		//deliver(m)
		std::cout <<"[DELIVER] mensagem \"" << nodo[recebeu].last[msg_decide[enviou].idorigem].m << "\" recebida do nodo " << enviou <<" foi entregue para a aplicacao pelo processo " << recebeu << " no tempo {" << time() << "}\n\n";

		for(int i = 0; i < 5; i++){
			//copia os primeiros 5 caracteres da mensagem recebida, para saber se
			//foi brcast de decisao ou de propose
			comp[i] = nodo[recebeu].last[msg_decide[enviou].idorigem].m[i];
			// std::cout << "-----------------" << comp[i] << "\n";
		}

/*
		if(comp == "myset" || comp == "myseT"){
			//quando faz deliver do brcast de propose, atualiza os vetores do consenso
			nodo[recebeu].correct_this_round[rodada].push_back(msg_decide[enviou].idorigem);
			//unir o meu proposal_set com o de quem me enviou
			//percorrer o proposal_set de quem enviou, verificando se já tem no de quem recebeu
			//ou nao, se nao tiver entao adiciona
			for(int contador = 0; contador < nodo[enviou].proposal_set[comp == "myset" ? rodada : rodada - 1].size(); contador++){
				//existe algum o valor do proposal_set de quem enviou no proposal_set de quem recebeu?
				//retorna true, caso exista
				val = nodo[enviou].proposal_set[comp == "myset" ? rodada : rodada - 1][contador];
				// printf("AAAAAAAAAAAAAA %d\n", val);
				rescon = std::any_of(nodo[recebeu].proposal_set[comp == "myset" ? rodada : rodada - 1].begin(), nodo[recebeu].proposal_set[comp == "myset" ? rodada : rodada - 1].end(), [val] (auto const &elem){
					return elem == val;
				});

				if(!rescon){
					// printf("%d - nao existe no meu proposal_set (%d)\n", recebeu, val);
					//adiciona o valor ao meu proposal_set, pois acabei de recebe-lo
					nodo[recebeu].proposal_set[comp == "myset" ? rodada : rodada - 1].push_back(val);
				}
			}

			verify(recebeu);
		} else
		*/
		 if(comp == "decid"){
			//quando faz brcast de decisao, apenas propaga a decisao para os outros nodos
			//mas apenas se pi esta correto e ainda nao decidiu
			if(status(nodo[recebeu].id == 0) && nodo[recebeu].decided == -1){
				printf("*** O nodo %d decide pelo valor %d que foi recebido do nodo %d\n", recebeu, nodo[enviou].decided, enviou);
				nodo[recebeu].decided = nodo[enviou].decided;
				// printf("##### nodo %d decidiu pelo valor %d, recebido do nodo %d\n", recebeu, nodo[recebeu].decided, enviou);

				//armazena em mensagens todas as mensagens ja enviadas pelo broadcast,
				//contendo o id de origem e o timestamp (unico para cada mensagem)
				//--- transforma a string em um tmsg ---
				mensagens.push_back(tmsg{'T', "decid " + std::to_string(nodo[recebeu].decided), nodo[recebeu].idr, timestamp});
				tamp = mensagens.size()-1;
				// std::cout << "Mensagem armazenada::::::::::::::::::" << mensagens[mensagens.size()-1].m << "\n";

				// rodada = 0;
				nodo_token = recebeu;
				//incrementa o timestamp sempre que gera uma nova mensagem
				timestamp++;
				schedule(brcast_dec, 0.1, recebeu);
			}
		}

		if(status(nodo[msg_decide[enviou].idorigem].id) != 0){
			// std::cout <<"Fazendo novo broadcast para os vizinhos sem-falha... " << "\n";
			schedule(brcast_dec, 0.1, recebeu);
			return;
		}
	}
	//encontrar identificador do cluster s de i que contem j
	for(int c = 0; c < tests[recebeu].size; c++){
		// printf("Agora vai calcular o cluster...\n");
		if(tests[recebeu].vector[c] == enviou){
			etp = tests[recebeu].etapa[c];
			// printf("Cluster do %d para o %d: %d\n", recebeu, enviou, etp);
			break;
		}
	}
	// print_tests();
	//retransmitir aos vizinhos corretos na arvore de source(m)
	//que pertencem ao cluster s que contém elementos
	//corretos de g

	for(int i = 0; i < N; i ++){
		for(int j = 0; j < tests[i].size; j++){
			for(int k = 1; k <= etp - 1; k++){
				if(tests[i].vector[j] == recebeu && tests[i].etapa[j] == k && status(nodo[i].id) == 0){
					// existe algum elemento em ack_set que respeite <j, k, m>?
					//retorna true, caso exista
					res = std::any_of(nodo[recebeu].ack_set.begin(), nodo[recebeu].ack_set.end(), [i, enviou] (auto const &elem){
						return elem.idorigem == enviou && elem.iddestino == nodo[i].idr && !(elem.m.m.compare(msg_decide[enviou].m));
					});
					//if <j,k,m> nao pertence ack_set(i)
					// j = enviou, k = ff_neighbor (aqui eh o nodo[i])
					if(!res){
						nodo[recebeu].ack_set.insert(tset{enviou, nodo[i].idr, msg_decide[enviou]});
						printf("[RBCAST] processo %d envia mensagem para processo %d\n", recebeu, nodo[i].idr);
						freceive_dec(recebeu, nodo[i].idr);
					}
				}
			}
		}
	}
	checkacks(nodo[enviou], msg_decide[enviou], 1);
}

void freceive(int enviou, int recebeu){
	int k, etp, val, tamp;
	bool res, rescon;
	std::string comp("strin");
	if(nodo[recebeu].last[msg_propose[enviou].idorigem].type == 'N'
	|| msg_propose[enviou].timestamp > nodo[recebeu].last[msg_propose[enviou].idorigem].timestamp){
		//last_i[source(m)] <- m
		//Atualiza o last do nodo atual com a mensagem que acabou
		//de ser recebida do outro nodo
		nodo[recebeu].last[msg_propose[enviou].idorigem].type = msg_propose[enviou].type;
		nodo[recebeu].last[msg_propose[enviou].idorigem].m.assign(msg_propose[enviou].m);
		nodo[recebeu].last[msg_propose[enviou].idorigem].idorigem = msg_propose[enviou].idorigem;
		nodo[recebeu].last[msg_propose[enviou].idorigem].timestamp = msg_propose[enviou].timestamp;

		msg_propose[recebeu].type = msg_propose[enviou].type;
		msg_propose[recebeu].m.assign(msg_propose[enviou].m);
		msg_propose[recebeu].idorigem = msg_propose[enviou].idorigem;
		msg_propose[recebeu].timestamp = msg_propose[enviou].timestamp;

		//deliver(m)
		std::cout <<"[DELIVER] mensagem \"" << nodo[recebeu].last[msg_propose[enviou].idorigem].m << "\" recebida do nodo " << enviou <<" foi entregue para a aplicacao pelo processo " << recebeu << " no tempo {" << time() << "}\n\n";

		for(int i = 0; i < 5; i++){
			//copia os primeiros 5 caracteres da mensagem recebida, para saber se
			//foi brcast de decisao ou de propose
			comp[i] = nodo[recebeu].last[msg_propose[enviou].idorigem].m[i];
			// std::cout << "-----------------" << comp[i] << "\n";
		}

		if(comp == "myset" || comp == "myseT"){
			//quando faz deliver do brcast de propose, atualiza os vetores do consenso

			// std::cout << comp;
			//alteracao minha!!

			if(comp == "myseT")
				for(int i = 0; i < nodo[recebeu].correct_this_round[rodada - 1].size(); i++){
					nodo[recebeu].correct_this_round[rodada].push_back(nodo[recebeu].correct_this_round[rodada - 1][i]);
					// printf("VALOR NO VETOR CTR[R-1] %d: \n", nodo[recebeu].correct_this_round[rodada - 1][i]);
				}

			nodo[recebeu].correct_this_round[rodada].push_back(msg_propose[enviou].idorigem);
			//unir o meu proposal_set com o de quem me enviou
			//percorrer o proposal_set de quem enviou, verificando se já tem no de quem recebeu
			//ou nao, se nao tiver entao adiciona
			for(int contador = 0; contador < nodo[enviou].proposal_set[comp == "myset" ? rodada : rodada - 1].size(); contador++){
				//existe algum o valor do proposal_set de quem enviou no proposal_set de quem recebeu?
				//retorna true, caso exista
				val = nodo[enviou].proposal_set[comp == "myset" ? rodada : rodada - 1][contador];
				// printf("AAAAAAAAAAAAAA %d\n", val);
				rescon = std::any_of(nodo[recebeu].proposal_set[comp == "myset" ? rodada : rodada - 1].begin(), nodo[recebeu].proposal_set[comp == "myset" ? rodada : rodada - 1].end(), [val] (auto const &elem){
					return elem == val;
				});

				if(!rescon){
					// printf("%d - nao existe no meu proposal_set (%d)\n", recebeu, val);
					//adiciona o valor ao meu proposal_set, pois acabei de recebe-lo
					nodo[recebeu].proposal_set[comp == "myset" ? rodada : rodada - 1].push_back(val);
				}
			}
			// printf("Tinha que chamar a verify\n");
			verify(recebeu);
		}
		/*
		else if(comp == "decid"){
			//quando faz brcast de decisao, apenas propaga a decisao para os outros nodos
			//mas apenas se pi esta correto e ainda nao decidiu
			if(status(nodo[recebeu].id == 0) && nodo[recebeu].decided == -1){
				nodo[recebeu].decided = nodo[enviou].decided;
				// printf("##### nodo %d decidiu pelo valor %d, recebido do nodo %d\n", recebeu, nodo[recebeu].decided, enviou);

				//armazena em mensagens todas as mensagens ja enviadas pelo broadcast,
				//contendo o id de origem e o timestamp (unico para cada mensagem)
				//--- transforma a string em um tmsg ---
				mensagens.push_back(tmsg{'T', "decid " + std::to_string(nodo[recebeu].decided), nodo[recebeu].idr, timestamp});
				tamp = mensagens.size()-1;
				// std::cout << "Mensagem armazenada::::::::::::::::::" << mensagens[mensagens.size()-1].m << "\n";

				// rodada = 0;
				nodo_token = recebeu;
				//incrementa o timestamp sempre que gera uma nova mensagem
				timestamp++;
				schedule(broadcast, 0.1, recebeu);
			}
		}
		*/

		if(status(nodo[msg_propose[enviou].idorigem].id) != 0){
			// std::cout <<"Fazendo novo broadcast para os vizinhos sem-falha... " << "\n";
			schedule(broadcast, 0.1, recebeu);
			return;
		}
	}
	//encontrar identificador do cluster s de i que contem j
	for(int c = 0; c < tests[recebeu].size; c++){
		// printf("Agora vai calcular o cluster...\n");
		if(tests[recebeu].vector[c] == enviou){
			etp = tests[recebeu].etapa[c];
			// printf("Cluster do %d para o %d: %d\n", recebeu, enviou, etp);
			break;
		}
	}
	// print_tests();
	//retransmitir aos vizinhos corretos na arvore de source(m)
	//que pertencem ao cluster s que contém elementos
	//corretos de g

	for(int i = 0; i < N; i ++){
		for(int j = 0; j < tests[i].size; j++){
			for(int k = 1; k <= etp - 1; k++){
				if(tests[i].vector[j] == recebeu && tests[i].etapa[j] == k && status(nodo[i].id) == 0){
					// existe algum elemento em ack_set que respeite <j, k, m>?
					//retorna true, caso exista
					res = std::any_of(nodo[recebeu].ack_set.begin(), nodo[recebeu].ack_set.end(), [i, enviou] (auto const &elem){
						return elem.idorigem == enviou && elem.iddestino == nodo[i].idr && !(elem.m.m.compare(msg_propose[enviou].m));
					});
					//if <j,k,m> nao pertence ack_set(i)
					// j = enviou, k = ff_neighbor (aqui eh o nodo[i])
					if(!res){
						nodo[recebeu].ack_set.insert(tset{enviou, nodo[i].idr, msg_propose[enviou]});
						printf("[RBCAST] processo %d envia mensagem para processo %d\n", recebeu, nodo[i].idr);
						freceive(recebeu, nodo[i].idr);
					}
				}
			}
		}
	}
	checkacks(nodo[enviou], msg_propose[enviou], 2);
}


//funcao chamada quando o processo i detecta o j como falho
void crash(tnodo j){
	int etp = 0, k = 0;
	bool r;
	//IF remover acks pendentes para <j,*,*>
	//ELSE enviar m para vizinho k, se k existir
	for(std:: set<tset>::iterator cont = nodo[token].ack_set.begin(); cont != nodo[token].ack_set.end(); cont++){
		if(cont->idorigem == j.idr)
			nodo[token].ack_set.erase(cont);
		else if(cont->iddestino == j.idr){
			//encontrar identificador do cluster s de i que contem j
			for(int c = 0; c < tests[token].size; c++)
				if(tests[token].vector[c] == j.idr){
					etp = tests[token].etapa[c];
					break;
				}
			for(std:: set<tset>::iterator cont2 = nodo[token].ack_set.begin(); cont2 != nodo[token].ack_set.end(); cont2++){
				//Se a mensagem eh a mesma que estamos analisando no for mais externo
				//se o nodo destino dessa mensagem achada esta sem-falha
				//e se esse nodo esta no mesmo cluster (s) que o nodo que falhou estava no nodo i
				if(!(cont2->m.m.compare(cont->m.m)) && status(nodo[cont2->iddestino].id) == 0 && tests[token].etapa[cont2->iddestino] == etp){
					//k <- ff_neighbor_i(s)
					for(int i = 0; i < tests[token].size; i++){
						if(tests[token].etapa[i] == etp && status(nodo[tests[token].vector[i]].id) == 0){
							k = tests[token].vector[i];
							// printf("Encontrou o ff_neighbor, que eh: %d", k);
							break;
						}
					}
					// printf("Vai verificar se alguem mandou mensagem para o ff_neighbor\n");
					//existe algum elemento em ack_set que respeite <*, k, m>?
					//retorna true, caso exista
					// --- cont eh do ..primeiro for, que esta passando por todos os elementos do ack_set
					// --- k eh o primeiro nodo sem falha obtido pela ff_neighbor
					r = std::any_of(nodo[token].ack_set.begin(), nodo[token].ack_set.end(), [cont, k] (auto const &elem){
						return elem.idorigem == cont->idorigem && elem.iddestino == k && !(elem.m.m.compare(cont->m.m));
					});
					//se nao encontrou o elemento, adiciona
					if(!r){
						// printf("Ninguem mandou :( vamos mandar agora\n");
						nodo[token].ack_set.insert(tset{cont->idorigem, k, cont->m});
						// send_msg(cont->m.m, cont2->iddestino, nodo[k]);
						//VERIFICAR MUUUUUUUUUUUITO ESSA FUNCAO HAHAHAH
						printf("--> Enviando mensagem do nodo %d para o nodo %d apos detectar %d falho\n", token, k, j.idr);
						freceive(token, k);
					}
				}
			}
		}
	}
	//fora do for
	//garantir a entrega da mensagem mais atual a todos os processos corretos
	//em dest(m) da ultima mensagem recebida de j (processo que falhou)
	//if last(i)[j] != vazio
	// printf("Chega aqui, pelo menos\n");
	// std::cout << nodo[token].last[j.idr].type << "\n";
	if(nodo[token].last[j.idr].type != 'N'){
		// printf("Sera que entra no if?\n");
		//existe algum elemento em ack_set que respeite <*, i, m>?
		//retorna true, caso exista
		//--- existe no ack_set de j (nodo falho) o registro de que eu (i) sou
		//um destinatario da ultima mensagem que eu recebi de j?
		//i E dest(last[j])
		r = std::any_of(j.ack_set.begin(), j.ack_set.end(), [j] (auto const &elem){
			return elem.iddestino == token && !(elem.m.m.compare(nodo[token].last[j.idr].m));
		});
		if(r){
			// printf("Aqui ele deve enviar a mensagem pro proximo do cluster\n");
			// broadcast(nodo[token].last[j.idr]);
			msg_propose[token].type = nodo[token].last[j.idr].type;
			msg_propose[token].m.assign(nodo[token].last[j.idr].m);
			msg_propose[token].idorigem = nodo[token].last[j.idr].idorigem;
			msg_propose[token].timestamp = nodo[token].last[j.idr].timestamp;
			// printf("Broadcast do crash\n");
			schedule(broadcast, 0.1, token);
		}
	}
}

/*---------------fim funcoes broadcast-----------------*/


//funcao que printa o vetor state de todos os nodos
void print_state(std:: vector<tnodo> &nodo, int n){

	// for(int i = 0; i < n; i++)
	// 	if(status(nodo[i].id) == 0)
	// 		printf("nodo sem falha %d\n", i);


	printf ("\nVetor STATE(i): ");
	for (int i = 0; i < n; i++)
		printf ("%d  ", i);
	printf ("\n");
	printf ("-------------------------------------\n");

	for (int i = 0; i < n; i++){
		if(status(nodo[i].id) == 0){
			printf (">     Nodo %d | ", i);
			for (int j = 0; j < n; j++)
					if(j < 9)
						printf (" %d ", nodo[i].state[j]);
					else
						printf ("  %d ", nodo[i].state[j]);
			printf("\n");
		}
	}
	printf("\n");
}

void print_init(){
	printf ("===========================================================\n");
	printf ("         Execucao do algoritmo V-Cube\n");
	printf ("         Aluna: Acacia dos Campos da Terra\n");
	printf ("         Professor: Elias P. Duarte Jr.\n");
	printf ("===========================================================\n\n");
}

void print_end(int r, int n){
	//apos o fim do tempo, printa os vetores states
	printf("\n--------------------------------------------------------------\n");
	printf("                       RESULTADOS\n");
	printf("\nNúmero de rodadas total do programa: %d\n", r);
	printf("\nVetor STATE ao final do diagnostico:\n");
	print_state(nodo, n);
}


int main(int argc, char const *argv[]) {
	static int event, r, i, aux, logtype, etp, k, x;
	static int nodosemfalha = 0, nodofalho = 0, nrodadas = 0, ntestes = 0, totalrodadas = 0;
	static char fa_name[5];	//facility representa o objeto simulado
	bool res, resb = true;
	int idx = -1;

//-------variáveis dos eventos passados por arquivo---------
	char evento[7];
	int processo;
	float tempo;

	 if(argc != 3){
		puts("Uso correto: ./vcube <arquivo> -parametro (-r ou -c)");
		exit(1);
	}

	//logtype, if 0 - reduced, if 1 - complete
	if(strcmp("-c", argv[2]) == 0)
		logtype = 1;
	else if(strcmp("-r", argv[2]) == 0)
		logtype = 0;
	else{
		printf("Parametro incorreto (-c ou -r)\n");
		exit(1);
	}

	//o arquivo foi chamado de tp por nenhum motivo especifico
	//faz a leitura do numero de nodos
	FILE *tp = fopen(argv[1], "r");
	if (tp != NULL)
		fscanf(tp, "%d\n", &N);
	else
		printf("Erro ao ler arquivo\n");
	fclose(tp);

	smpl(0, "programa vcube");
	reset();
	stream(1);
	// nodo = (tnodo*) malloc(sizeof(tnodo)*N);
	nodo.resize(N);

	for (i = 0; i < N; i++) {
	 	memset(fa_name, '\0', 5);
	 	printf(fa_name, "%d", i);
	 	nodo[i].id = facility(fa_name, 1);
		nodo[i].idr = i;

		//para cada nodo cria e inicializa vetor state com -1(UNKNOWN)
		nodo[i].state = (int*) malloc (sizeof(int)*N);

		msg_propose.resize(N);
		msg_decide.resize(N);
		msg_round.resize(N);
		ultimo_nodo.resize(N);
		ultimo_nodo_dec.resize(N);
		ultimo_nodo_round.resize(N);

		nodo[i].correct_this_round.resize(N + 1);
		nodo[i].proposal_set.resize(N + 1);
		nodo[i].decided = -1;

		//para cada nodo cria vetor last
		nodo[i].last.resize(N);
		for (int j = 0; j < N; j++){
			nodo[i].state[j] = 0;
			nodo[i].last[j].type = 'N';
			nodo[i].last[j].idorigem = -1;
			nodo[i].last[j].timestamp = -1;

			//no inicio todos os nodos iniciam sem-falha -> na primeira rodada tbm (rodada 0)
			nodo[i].correct_this_round[0].push_back(j);
			// std::cout << "Foi inserido: " << i << " -> " << nodo[i].correct_this_round[0][j] << "\n";
		}
	 }

	 // exemplo:
	//  nodo[0].correct_this_round.resize(5); //nodo 0, 5 rodadas
	//  nodo[3].correct_this_round.resize(2); //nodo 3, 2 rodadas
	//  nodo[0].correct_this_round[0].resize(3); //nodo 0, 5 rodadas e 3 nodos sem-falha na primeira rodada
	//  nodo[0].correct_this_round[0][0] = 454; //o primeiro nodo sem-falha da rodada foi o 454
	 //
	//  	printf("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAa\n");
	//  	 std::cout << nodo[0].correct_this_round.size() << "\n";
	// 	 std::cout << nodo[3].correct_this_round.size() << "\n";
	// 	 std::cout << nodo[0].correct_this_round[0][0] << "\n";

	 print_init();
	 /*schedule inicial*/
	 for (i = 0; i < N; i++)
	 	schedule(test, 30.0, i);

	tp = fopen(argv[1], "r");
	fscanf(tp, "%d\n", &N);
	while(!feof(tp)){
		fscanf(tp, "%s %f %d\n", evento, &tempo, &processo);
		// printf("%s %f %d\n", evento, tempo, processo);
		schedule((strcmp("fault", evento) == 0 ? fault : (strcmp("repair", evento) == 0 ?
		repair : (strcmp("broadcast", evento) == 0 ? broadcast : (strcmp("new_msg", evento) == 0 ?
		new_msg : (strcmp("propose", evento) == 0 ? propose : test))))), tempo, processo);
		//escalona os eventos. Faz a verificação de string pois o schedule não aceita string como parâmetro
	}
	fclose(tp);

	aux = N;
	 printf("Programa inicializa - todos os nodos estao *sem-falha*\n");
	 for(s = 0; aux != 1; aux /= 2, s++);//for para calcular o valor de S (log de n)
	 tests = testes(N, s, nodo); //calcula quais os testes executados
	//  for(i = 0; i < N; i++){//printa os testes executados por cada nodo, apos ser calculado
	// 	 printf("O nodo %d testa os nodos: ", i);
	// 	 for(int j = 0; j < tests[i].size; j++)
	// 		 printf("%d ", tests[i].vector[j]);
	// 	 printf("\n");
	//  }

	// schedule(broadcast, 1.0, token);

	 while(time() < 250.0) {
	 	cause(&event, &token); //causa o proximo evento
	 	switch(event) {
	 		case test:
	 		if(status(nodo[token].id) != 0){
				// nodofalho++;  //contabiliza nodos FALHOS
				break; //se o nodo for falho, então quebra
			}else{
				nodosemfalha++;  //contabiliza nodos SEM-FALHA
			}

			//se o state de token for um numero impar, esta desatualizado
			//esta marcando como falho (impar = falho, par = sem-falha)
			//acrescenta-se +1, para indicar que esta sem-falha e ficar certo
			if((nodo[token].state[token] % 2) != 0)
				nodo[token].state[token]++;
			printf("[%5.1f] ", time());
			printf("Nodo %d testa: ", token);
			for(int i = 0; i < tests[token].size; i++){
				printf("%d ", tests[token].vector[i]);
				if(status(nodo[tests[token].vector[i]].id) == 0) {//se o nodo estiver sem-falha
					ntestes++;  //contabiliza os testes realizados

					//atualiza o valor no state, caso esteja desatualizado
					if((nodo[token].state[tests[token].vector[i]] % 2) != 0){
						if(nodo[token].state[tests[token].vector[i]] != -1)
							printf("(nodo detecta evento: nodo %d sem-falha) ", tests[token].vector[i]);
						nodo[token].state[tests[token].vector[i]]++;
					}

					for(int j = 0; j < N; j++){//for para verificar as novidades
						if(nodo[token].state[j] == -1){
							//caso seja o inicio do programa, atualiza o state com 0
							nodo[token].state[j] = 0;
						}else if(nodo[token].state[j] < nodo[tests[token].vector[i]].state[j]){
							//caso nao seja o inicio e o valor do state do token seja menor
							//que o do state de j, entao copia as novidades
							nodo[token].state[j] = nodo[tests[token].vector[i]].state[j];
							printf("(nodo %d obtem info nodo %d: nodo %d falho) ", token, tests[token].vector[i], j);

							crash(nodo[j]);
						}
					}
				} else if((nodo[token].state[tests[token].vector[i]] % 2) == 0) {
					//caso o nodo esteja falho e o state esteja desatualizado
					//ou seja, esta como nao falho, mas na verdade esta falho
					//entao atualiza o vetor state
					nodo[token].state[tests[token].vector[i]]++;
					printf("(nodo detecta evento: nodo %d falho) ", tests[token].vector[i]);

					// printf("------- %d\n", nodo[l].idr);
					//envia o nodo que falhou
					crash(nodo[tests[token].vector[i]]);
				}
			}
			printf("\n");


			// printf("\n\t\t>>> nodo falho: %d nodo sem falha: %d\n\n", nodofalho, nodosemfalha);
// -------------------------------verificacao para numero de rodadas-------------------------------------------------------------
			if((nodofalho + nodosemfalha == N) && time() > 30.0){  //so entra se todos foram testados
				int nodosf, i, end = 1;
				nodosemfalha = 0;

				for (nodosf = 0; nodosf < N; nodosf++){  //encontra o primeiro nodo SEM-FALHA
					if (status(nodo[nodosf].id) == 0)
						break;
				}

				if (nodosf != N-1){ //verifica se nao eh o ultimo, para evitar seg fault
					for (i = nodosf + 1; i < N; i++){ //compara o vetor de nodosf com os demais
						if (status(nodo[i].id) != 0)//se for nodo FALHO apenas passa para o proximo
							continue;

						for (int j = 0; j < N; j++){  //compara se state dos SEM-FALHA sao iguais
							if (nodo[nodosf].state[j] != nodo[i].state[j])
								end = 0;//significa que os vetores estao diferentes
						}
					}
				}
				nrodadas++;//aumenta o numero de rodadas, independente dos vetores estarem iguais
				totalrodadas++;//aumenta as rodadas do programa todo
				if(logtype)
					print_state(nodo, N);
				printf("\t------ Fim da rodada %d ------\n", totalrodadas);

				if (i == N && end == 1){
					//todos os vetores SEM-FALHA foram comparados e sao iguais
					//entao o evento foi diagnosticado, printa a quantidade de rodadas e testes necessarios
					// printf ("O evento precisou de %d rodadas e %d testes para ser diagnosticado\n", nrodadas, ntestes);
				}
				// print_tests();
			}

// ---------------------------------------fim da verificacao de rodadas-----------------------------------------------------

	 		schedule(test, 30.0, token);
	 		break;

	 		case fault:
			// print_state(nodo, N);
			//atualiza os valores para continuar contando
			nodosemfalha = 0;
			nodofalho++;
			nrodadas = 0;
			ntestes = 0;
	 		r = request(nodo[token].id, token, 0);
	 		if(r != 0) {
	 			puts("Impossível falhar nodo");
	 			exit(1);
	 		}
				printf("EVENTO: O nodo %d falhou no tempo %5.1f\n", token, time());

//-----------------------a cada evento, recalcula o vetor tests----------------------------------
			free(tests);
			tests = testes(N, s, nodo); //calcula quais os testes executados
			// for(i = 0; i < N; i++){//printa os testes executados por cada nodo, apos ser calculado
			// 	printf("O nodo %d testa os nodos: ", i);
			// 	for(int j = 0; j < tests[i].size; j++)
			// 		printf("%d ", tests[i].vector[j]);
			// 	printf("\n");
			// }
			break;

	 		case repair:
			// print_state(nodo, N);
			//atualiza os valores para continuar contando
			nodofalho--; //se recuperou, tem um nodo falho a menos
			nodosemfalha = 0;
			nrodadas = 0;
			ntestes = 0;

	 		release(nodo[token].id, token);
	 		printf("EVENTO: O nodo %d recuperou no tempo %5.1f\n", token, time());

//-----------------------a cada evento, recalcula o vetor tests----------------------------------
			free(tests);
			tests = testes(N, s, nodo); //calcula quais os testes executados
			// for(i = 0; i < N; i++){//printa os testes executados por cada nodo, apos ser calculado
			// 	printf("O nodo %d testa os nodos: ", i);
			// 	for(int j = 0; j < tests[i].size; j++)
			// 		printf("%d ", tests[i].vector[j]);
			// 	printf("\n");
			// }
			schedule(test, 30.0, token);
			break;

			case brcast_dec:
			resb = true;
			//if source(m) == i
			if(msg_decide[token].idorigem == token && status(nodo[token].id) == 0){
				//isso aqui não vai gerar look infinito não? HAHAHAHAHAHAHAHAHAH
				while(resb){
					//existe algum elemento em ack_set que respeite <i, *, last_i[i]>?
					//retorna true, caso exista
					resb = std::any_of(nodo[token].ack_set.begin(), nodo[token].ack_set.end(), [] (auto const &elem){
						return elem.idorigem == token && !(elem.m.m.compare(nodo[token].last[token].m)) && elem.m.idorigem == nodo[token].last[token].idorigem;
					});
				}

				//last_i[i] = m
				nodo[token].last[token].type = msg_decide[token].type;
				nodo[token].last[token].m.assign(msg_decide[token].m);
				nodo[token].last[token].idorigem = msg_decide[token].idorigem;
				nodo[token].last[token].timestamp = msg_decide[token].timestamp;

				//deliver(m)
				std::cout <<"[DELIVER] mensagem \"" << nodo[token].last[token].m << "\" foi entregue para a aplicacao pelo processo " << token << "\n\n";

			}
			//enviar a todos os vizinhos corretos que pertencem ao cluster s
			for(int i = 0; i < N; i ++){
				for(int j = 0; j < tests[i].size; j++){
					if(tests[i].vector[j] == token){
						// printf("token: %d\n", token);
						// printf("i: %d\n", i);
						printf("[RBCAST] processo %d envia mensagem para processo %d\n", token, nodo[i].idr);
						freceive_dec(token, nodo[i].idr);
					}
				}
			}
			break;

			case receive_ack:
				// x | <x,j,m> pertence ack_set(i)
				for(std:: set<tset>::iterator cont = nodo[token].ack_set.begin(); cont != nodo[token].ack_set.end(); cont++){
					// std::cout << "Origem: " << cont->idorigem << " Destino: " << cont->iddestino << "\n";
					if(cont->iddestino == ultimo_nodo[token] && !(cont->m.m.compare(msg_propose[token].m))){
						idx = cont->idorigem;
					}
				}
				//if meu id != x, identifica nodo e chama checkacks
				if(idx != -1 && idx != nodo[token].idr){
					// printf("%d\n", idx);
					checkacks(nodo[idx], msg_propose[token], 2);
				}
				break;

				case receive_ack_round:
					// x | <x,j,m> pertence ack_set(i)
					for(std:: set<tset>::iterator cont = nodo[token].ack_set.begin(); cont != nodo[token].ack_set.end(); cont++){
						// std::cout << "Origem: " << cont->idorigem << " Destino: " << cont->iddestino << "\n";
						if(cont->iddestino == ultimo_nodo_round[token] && !(cont->m.m.compare(msg_round[token].m))){
							idx = cont->idorigem;
						}
					}
					//if meu id != x, identifica nodo e chama checkacks
					if(idx != -1 && idx != nodo[token].idr){
						// printf("%d\n", idx);
						checkacks(nodo[idx], msg_round[token], 3);
					}
					break;

				case receive_ack_dec:
					// x | <x,j,m> pertence ack_set(i)
					for(std:: set<tset>::iterator cont = nodo[token].ack_set.begin(); cont != nodo[token].ack_set.end(); cont++){
						// std::cout << "Origem: " << cont->idorigem << " Destino: " << cont->iddestino << "\n";
						if(cont->iddestino == ultimo_nodo_dec[token] && !(cont->m.m.compare(msg_decide[token].m))){
							idx = cont->idorigem;
						}
					}
					//if meu id != x, identifica nodo e chama checkacks
					if(idx != -1 && idx != nodo[token].idr){
						// printf("%d\n", idx);
						checkacks(nodo[idx], msg_decide[token], 1);
					}
					break;

			case new_msg:
			int tam;
				//armazena em mensagens todas as mensagens ja enviadas pelo broadcast,
				//contendo o id de origem e o timestamp (unico para cada mensagem)
				//--- transforma a string em um tmsg ---
				mensagens.push_back(tmsg{'T', "teste "+ std::to_string(timestamp), nodo[token].idr, timestamp});
				tam = mensagens.size()-1;
				// std::cout << "Mensagem armazenada::::::::::::::::::" << mensagens[mensagens.size()-1].m << "\n";

				msg_propose[token].type = mensagens[tam].type;
				msg_propose[token].m.assign(mensagens[tam].m);
				msg_propose[token].idorigem = mensagens[tam].idorigem;
				msg_propose[token].timestamp = mensagens[tam].timestamp;

				//incrementa o timestamp sempre que gera uma nova mensagem
				timestamp++;
				break;


				case broadcast:
				//if source(m) == i
				resb = true;
				if(msg_propose[token].idorigem == token && status(nodo[token].id) == 0){
					//isso aqui não vai gerar look infinito não? HAHAHAHAHAHAHAHAHAH
					while(resb){
						//existe algum elemento em ack_set que respeite <i, *, last_i[i]>?
						//retorna true, caso exista
						resb = std::any_of(nodo[token].ack_set.begin(), nodo[token].ack_set.end(), [] (auto const &elem){
							return elem.idorigem == token && !(elem.m.m.compare(nodo[token].last[token].m)) && elem.m.idorigem == nodo[token].last[token].idorigem;
						});
					}

					//last_i[i] = m
					nodo[token].last[token].type = msg_propose[token].type;
					nodo[token].last[token].m.assign(msg_propose[token].m);
					nodo[token].last[token].idorigem = msg_propose[token].idorigem;
					nodo[token].last[token].timestamp = msg_propose[token].timestamp;

					//deliver(m)
					std::cout <<"[DELIVER] mensagem \"" << nodo[token].last[token].m << "\" foi entregue para a aplicacao pelo processo " << token << "\n\n";
					nodo[token].correct_this_round[rodada].push_back(token);

					verify(token);

				}
				//enviar a todos os vizinhos corretos que pertencem ao cluster s
				for(int i = 0; i < N; i ++){
					for(int j = 0; j < tests[i].size; j++){
						if(tests[i].vector[j] == token){
							// printf("token: %d\n", token);
							// printf("i: %d\n", i);
							printf("[RBCAST] processo %d envia mensagem para processo %d\n", token, nodo[i].idr);
							freceive(token, nodo[i].idr);
						}
					}
				}
				break;

			case propose:
				//nodo token propoe um valor aleatorio
				//acrescenta ao proposal_set da primeira rodada
				//no algoritmo é 1, aqui usamos 0 e no final somaremos + 1 apenas
				//para a contagem de rodadas ficar certa

				int v;
				v = rand() % 50;
				printf("---> O nodo %d propos o valor: %d\n", token, v);
				nodo[token].proposal_set[1].push_back(v);

				//faz broadcast informando qual o nodo token
				//no algoritmo envia o proposal set, mas é global,
				//entao vamos fornecer a informacao e o nodo se encarrega
				//de pega-la. Enviamos tambem a rodada

				int tamp;
				//armazena em mensagens todas as mensagens ja enviadas pelo broadcast,
				//contendo o id de origem e o timestamp (unico para cada mensagem)
				//--- transforma a string em um tmsg ---
				mensagens.push_back(tmsg{'T', "myset rodada: "+ std:: to_string(rodada) + " token: " + std::to_string(token), nodo[token].idr, timestamp});
				tamp = mensagens.size()-1;
				// std::cout << "Mensagem armazenada::::::::::::::::::" << mensagens[mensagens.size()-1].m << "\n";

				msg_propose[token].type = mensagens[tamp].type;
				msg_propose[token].m.assign(mensagens[tamp].m);
				msg_propose[token].idorigem = mensagens[tamp].idorigem;
				msg_propose[token].timestamp = mensagens[tamp].timestamp;

				// rodada = 0;
				nodo_token = token;
				//incrementa o timestamp sempre que gera uma nova mensagem
				timestamp++;

				schedule(broadcast, 0.1, token);
			break;


			case broadcast_round:
			resb = true;
			//if source(m) == i
			if(msg_round[token].idorigem == token && status(nodo[token].id) == 0){
				//isso aqui não vai gerar look infinito não? HAHAHAHAHAHAHAHAHAH
				while(resb){
					//existe algum elemento em ack_set que respeite <i, *, last_i[i]>?
					//retorna true, caso exista
					resb = std::any_of(nodo[token].ack_set.begin(), nodo[token].ack_set.end(), [] (auto const &elem){
						return elem.idorigem == token && !(elem.m.m.compare(nodo[token].last[token].m)) && elem.m.idorigem == nodo[token].last[token].idorigem;
					});
				}

				//last_i[i] = m
				nodo[token].last[token].type = msg_round[token].type;
				nodo[token].last[token].m.assign(msg_round[token].m);
				nodo[token].last[token].idorigem = msg_round[token].idorigem;
				nodo[token].last[token].timestamp = msg_round[token].timestamp;

				//deliver(m)
				std::cout <<"[DELIVER] mensagem \"" << nodo[token].last[token].m << "\" foi entregue para a aplicacao pelo processo " << token << "\n\n";

			}
			rodada++;
			//enviar a todos os vizinhos corretos que pertencem ao cluster s
			for(int i = 0; i < N; i ++){
				for(int j = 0; j < tests[i].size; j++){
					if(tests[i].vector[j] == token){
						// printf("token: %d\n", token);
						// printf("i: %d\n", i);
						printf("[RBCAST] processo %d envia mensagem para processo %d\n", token, nodo[i].idr);
						freceive_round(token, nodo[i].idr);
					}
				}
			}
			break;


	 	}
	}

	print_end(totalrodadas, N);

	return 0;
}
