package com.github.ackintosh.graphql.dataloader

import com.github.ackintosh.graphql.repository.ItemRepository
import com.github.ackintosh.graphql.type.Item
import org.dataloader.BatchLoader
import org.springframework.stereotype.Component
import java.util.concurrent.CompletableFuture

@Component
class ItemDataLoader(
        val itemRepository: ItemRepository
) {
    fun loader() =
            BatchLoader<Int, Item> { keys: List<Int> ->
                CompletableFuture.supplyAsync { items(keys) }
            }

    private fun items(ids: List<Int>): List<Item> {
        println("ItemDataLoader")
        return itemRepository.find(ids)
    }
}
