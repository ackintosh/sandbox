package com.github.ackintosh.graphql.resolver

import com.coxautodev.graphql.tools.GraphQLResolver
import com.github.ackintosh.graphql.type.Item
import com.github.ackintosh.graphql.type.Recommend
import graphql.kickstart.execution.context.GraphQLContext
import graphql.schema.DataFetchingEnvironment
import org.springframework.stereotype.Component
import java.util.concurrent.CompletableFuture

@Component
class ItemResolver: GraphQLResolver<Recommend> {

    fun items(recommend: Recommend, environment: DataFetchingEnvironment): CompletableFuture<List<Item>> {
        println("ItemResolver::items()")
        val loader = environment.getContext<GraphQLContext>()
                .dataLoaderRegistry.get().getDataLoader<Int, Item>("itemDataLoader")

        return loader.loadMany(recommend.itemIds)
    }
}