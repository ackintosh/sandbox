package com.github.ackintosh.graphql.resolver

import com.coxautodev.graphql.tools.GraphQLResolver
import com.github.ackintosh.graphql.repository.ItemRepository
import com.github.ackintosh.graphql.type.Item
import com.github.ackintosh.graphql.type.Recommend
import org.springframework.stereotype.Component

@Component
class ItemResolver(
        val itemRepository: ItemRepository
): GraphQLResolver<Recommend> {

    fun items(recommend: Recommend): List<Item> {
        println("ItemResolver::items()")
        return itemRepository.find(recommend)
    }
}