interface CancellationToken {
  cancel: () => void
}

class CancellationToken {
  public static combine(...tokens: CancellationToken[]): CancellationToken {
    return {
      cancel: () => tokens.forEach(t => t.cancel())
    }
  }
  public static noop(): CancellationToken {
    return {
      cancel: () => { }
    }
  }
}

interface IPublisher<T> {
  listen(handler: { (data: T): void }): CancellationToken;
}

class Publisher<T> implements IPublisher<T> {
  private queue: boolean

  constructor(queue?: boolean) {
    this.queue = queue ? queue : false
  }

  private handlers: { (data: T): void; }[] = [];

  public listen(handler: { (data: T): void }) : CancellationToken {
      this.handlers.push(handler);
      return {
        cancel: () => this.handlers = this.handlers.filter(h => h !== handler)
      }
  }

  public publish(data: T) {
    if (this.queue)
      this.handlers.splice(0,1).forEach(h => h(data));
    else 
      this.handlers.slice(0).forEach(h => h(data));      
  }

  public expose(): IPublisher<T> {
      return this;
  }
}